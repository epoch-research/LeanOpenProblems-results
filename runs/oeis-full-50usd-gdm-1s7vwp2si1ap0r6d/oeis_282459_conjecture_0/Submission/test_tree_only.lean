import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/--
A282459: Number of composite numbers of the form $2n - 2^k + 1$ ($k > 0, 2^k < 2n + 1$).
-/
def A282459 (n : ℕ) : ℕ :=
  let upper_k : ℕ := log 2 (2 * n + 1)
  let s := Finset.Icc 1 upper_k
  let is_composite (m : ℕ) : Prop := 1 < m ∧ ¬ Nat.Prime m
  let seq_val (k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k
  Finset.card (Finset.filter (fun k : ℕ => is_composite (seq_val k)) s)

lemma A282459_pos_of_exists (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)))
    (h_comp : 1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k)) : A282459 n > 0 := by
  have h_comp' : (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k)) := h_comp
  unfold A282459
  dsimp
  have hk_filter : k ∈ Finset.filter (fun k => (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k))) (Finset.Icc 1 (log 2 (2 * n + 1))) := by
    rw [Finset.mem_filter]
    exact ⟨hk, h_comp'⟩
  have h_nonempty : (Finset.filter (fun k => (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k))) (Finset.Icc 1 (log 2 (2 * n + 1)))).Nonempty := by
    exact ⟨k, hk_filter⟩
  exact Finset.card_pos.mpr h_nonempty

lemma k_in_Icc (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2*n+1) : k ∈ Finset.Icc 1 (log 2 (2*n+1)) := by
  rw [Finset.mem_Icc]
  refine ⟨hk1, ?_⟩
  exact Nat.le_log_of_pow_le Nat.one_lt_two hk2

lemma dvd_of_mod_eq (N k p : ℕ) (hN : N % p = 2^k % p) (hk : 2^k ≤ N) : p ∣ N - 2^k := by
  have h_modeq : 2^k ≡ N [MOD p] := by
    exact hN.symm
  exact (Nat.modEq_iff_dvd' hk).mp h_modeq

lemma composite_of_dvd (N : ℕ) (k : ℕ) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ N - 2^k) (hgt : p < N - 2^k) (h1 : 1 < N - 2^k) :
    1 < N - 2^k ∧ ¬ Nat.Prime (N - 2^k) := by
  refine ⟨h1, ?_⟩
  intro h_prime
  have h_dvd_eq : p = N - 2^k := by
    exact ((Nat.Prime.dvd_iff_eq h_prime hp.ne_one).mp hdvd).symm
  omega

theorem oeis_282459_conjecture_0 : ∀ n : ℕ, n > 52 → A282459 n > 0 := by
  intro n hn
  rcases lt_or_ge n 2055 with h_small | h_large
  · sorry
  · have hN : 2 * n + 1 ≥ 4111 := by omega
    have hp3 : Nat.Prime 3 := Nat.prime_three
    have hp5 : Nat.Prime 5 := by decide
    have hp11 : Nat.Prime 11 := by decide
    have hp13 : Nat.Prime 13 := by decide
    have hp17 : Nat.Prime 17 := by decide
    have hp19 : Nat.Prime 19 := by decide
    have hp23 : Nat.Prime 23 := by decide
    have hp29 : Nat.Prime 29 := by decide
    have h_mod_3 : (2 * n + 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases (2 * n + 1) % 3
    · -- Case (2*n+1) % 3 = 0
      have h_mod_5 : (2 * n + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
      interval_cases (2 * n + 1) % 5
      · -- Case (2*n+1) % 5 = 0
        have h_mod_11 : (2 * n + 1) % 11 < 11 := Nat.mod_lt _ (by decide)
        interval_cases (2 * n + 1) % 11
        · -- Case (2*n+1) % 11 = 0
          have h_mod_13 : (2 * n + 1) % 13 < 13 := Nat.mod_lt _ (by decide)
          interval_cases (2 * n + 1) % 13
          · -- Case (2*n+1) % 13 = 0
            have h_mod_19 : (2 * n + 1) % 19 < 19 := Nat.mod_lt _ (by decide)
            interval_cases (2 * n + 1) % 19
            · -- Case (2*n+1) % 19 = 0
              have h_mod_29 : (2 * n + 1) % 29 < 29 := Nat.mod_lt _ (by decide)
              interval_cases (2 * n + 1) % 29
              · -- Case (2*n+1) % 29 = 0
                have h17 : (2 * n + 1) % 17 < 17 := Nat.mod_lt _ (by decide)
                interval_cases (2 * n + 1) % 17
                · -- Case % 17 = 0
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 231060472 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 110507182 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 431982622 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 452074837 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 150691612 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 170783827 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 331521547 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 190876042 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 50230537 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 210968257 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 371705977 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 70322752 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 1
                  have hk : 2^8 ≤ 2 * n + 1 := by omega
                  have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^8 := by
                    apply dvd_of_mod_eq (2 * n + 1) 8 17
                    · change (2 * n + 1) % 17 = 1
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^8 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                    exact composite_of_dvd (2 * n + 1) 8 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 8 h_in h_comp
                · -- Case % 17 = 2
                  have hk : 2^1 ≤ 2 * n + 1 := by omega
                  have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^1 := by
                    apply dvd_of_mod_eq (2 * n + 1) 1 17
                    · change (2 * n + 1) % 17 = 2
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^1 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                    exact composite_of_dvd (2 * n + 1) 1 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 1 h_in h_comp
                · -- Case % 17 = 3
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 203876887 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 83323597 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 404799037 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 424891252 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 123508027 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 143600242 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 304337962 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 163692457 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 23046952 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 183784672 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 344522392 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 43139167 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 4
                  have hk : 2^2 ≤ 2 * n + 1 := by omega
                  have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^2 := by
                    apply dvd_of_mod_eq (2 * n + 1) 2 17
                    · change (2 * n + 1) % 17 = 4
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^2 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                    exact composite_of_dvd (2 * n + 1) 2 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 2 h_in h_comp
                · -- Case % 17 = 5
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 339794812 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 219241522 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 78596017 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 98688232 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 259425952 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 279518167 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 440255887 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 299610382 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 158964877 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 319702597 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 18319372 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 179057092 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 6
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 176693302 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 56140012 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 377615452 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 397707667 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 96324442 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 116416657 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 277154377 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 136508872 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 457984312 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 156601087 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 317338807 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 15955582 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 7
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 13591792 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 355159447 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 214513942 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 234606157 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 395343877 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 415436092 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 114052867 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 435528307 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 294882802 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 455620522 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 154237297 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 314975017 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 8
                  have hk : 2^3 ≤ 2 * n + 1 := by omega
                  have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^3 := by
                    apply dvd_of_mod_eq (2 * n + 1) 3 17
                    · change (2 * n + 1) % 17 = 8
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^3 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                    exact composite_of_dvd (2 * n + 1) 3 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 3 h_in h_comp
                · -- Case % 17 = 9
                  have hk : 2^7 ≤ 2 * n + 1 := by omega
                  have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^7 := by
                    apply dvd_of_mod_eq (2 * n + 1) 7 17
                    · change (2 * n + 1) % 17 = 9
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^7 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                    exact composite_of_dvd (2 * n + 1) 7 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 7 h_in h_comp
                · -- Case % 17 = 10
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 448529152 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 327975862 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 187330357 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 207422572 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 368160292 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 388252507 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 86869282 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 408344722 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 267699217 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 428436937 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 127053712 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 287791432 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 11
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 285427642 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 164874352 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 24228847 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 44321062 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 205058782 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 225150997 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 385888717 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 245243212 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 104597707 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 265335427 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 426073147 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 124689922 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 12
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 122326132 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 1772842 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 323248282 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 343340497 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 41957272 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 62049487 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 222787207 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 82141702 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 403617142 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 102233917 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 262971637 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 423709357 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 13
                  have hk : 2^6 ≤ 2 * n + 1 := by omega
                  have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^6 := by
                    apply dvd_of_mod_eq (2 * n + 1) 6 17
                    · change (2 * n + 1) % 17 = 13
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^6 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                    exact composite_of_dvd (2 * n + 1) 6 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 6 h_in h_comp
                · -- Case % 17 = 14
                  have h23 : (2 * n + 1) % 23 < 23 := Nat.mod_lt _ (by decide)
                  interval_cases (2 * n + 1) % 23
                  · -- Case % 23 = 0
                    have h_eq : n = 258244057 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 1
                    have hk : 2^11 ≤ 2 * n + 1 := by omega
                    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
                      apply dvd_of_mod_eq (2 * n + 1) 11 23
                      · change (2 * n + 1) % 23 = 1
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^11 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                      exact composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 11 h_in h_comp
                  · -- Case % 23 = 2
                    have hk : 2^1 ≤ 2 * n + 1 := by omega
                    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
                      apply dvd_of_mod_eq (2 * n + 1) 1 23
                      · change (2 * n + 1) % 23 = 2
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^1 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                      exact composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 1 h_in h_comp
                  · -- Case % 23 = 3
                    have hk : 2^8 ≤ 2 * n + 1 := by omega
                    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
                      apply dvd_of_mod_eq (2 * n + 1) 8 23
                      · change (2 * n + 1) % 23 = 3
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^8 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                      exact composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 8 h_in h_comp
                  · -- Case % 23 = 4
                    have hk : 2^2 ≤ 2 * n + 1 := by omega
                    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
                      apply dvd_of_mod_eq (2 * n + 1) 2 23
                      · change (2 * n + 1) % 23 = 4
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^2 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                      exact composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 2 h_in h_comp
                  · -- Case % 23 = 5
                    have h_eq : n = 137690767 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 6
                    have hk : 2^9 ≤ 2 * n + 1 := by omega
                    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
                      apply dvd_of_mod_eq (2 * n + 1) 9 23
                      · change (2 * n + 1) % 23 = 6
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^9 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                      exact composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 9 h_in h_comp
                  · -- Case % 23 = 7
                    have h_eq : n = 459166207 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 8
                    have hk : 2^3 ≤ 2 * n + 1 := by omega
                    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
                      apply dvd_of_mod_eq (2 * n + 1) 3 23
                      · change (2 * n + 1) % 23 = 8
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^3 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                      exact composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 3 h_in h_comp
                  · -- Case % 23 = 9
                    have hk : 2^5 ≤ 2 * n + 1 := by omega
                    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
                      apply dvd_of_mod_eq (2 * n + 1) 5 23
                      · change (2 * n + 1) % 23 = 9
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^5 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                      exact composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 5 h_in h_comp
                  · -- Case % 23 = 10
                    have h_eq : n = 17137477 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 11
                    have h_eq : n = 177875197 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 12
                    have hk : 2^10 ≤ 2 * n + 1 := by omega
                    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
                      apply dvd_of_mod_eq (2 * n + 1) 10 23
                      · change (2 * n + 1) % 23 = 12
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^10 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                      exact composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 10 h_in h_comp
                  · -- Case % 23 = 13
                    have hk : 2^7 ≤ 2 * n + 1 := by omega
                    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
                      apply dvd_of_mod_eq (2 * n + 1) 7 23
                      · change (2 * n + 1) % 23 = 13
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^7 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                      exact composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 7 h_in h_comp
                  · -- Case % 23 = 14
                    have h_eq : n = 197967412 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 15
                    have h_eq : n = 358705132 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 16
                    have hk : 2^4 ≤ 2 * n + 1 := by omega
                    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
                      apply dvd_of_mod_eq (2 * n + 1) 4 23
                      · change (2 * n + 1) % 23 = 16
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^4 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                      exact composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 4 h_in h_comp
                  · -- Case % 23 = 17
                    have h_eq : n = 218059627 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 18
                    have hk : 2^6 ≤ 2 * n + 1 := by omega
                    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
                      apply dvd_of_mod_eq (2 * n + 1) 6 23
                      · change (2 * n + 1) % 23 = 18
                        omega
                      · exact hk
                    have h_gt : 23 < 2 * n + 1 - 2^6 := by omega
                    have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                      exact composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
                    exact A282459_pos_of_exists n 6 h_in h_comp
                  · -- Case % 23 = 19
                    have h_eq : n = 77414122 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 20
                    have h_eq : n = 238151842 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 21
                    have h_eq : n = 398889562 := by omega
                    subst h_eq
                    decide
                  · -- Case % 23 = 22
                    have h_eq : n = 97506337 := by omega
                    subst h_eq
                    decide
                · -- Case % 17 = 15
                  have hk : 2^5 ≤ 2 * n + 1 := by omega
                  have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^5 := by
                    apply dvd_of_mod_eq (2 * n + 1) 5 17
                    · change (2 * n + 1) % 17 = 15
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^5 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                    exact composite_of_dvd (2 * n + 1) 5 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 5 h_in h_comp
                · -- Case % 17 = 16
                  have hk : 2^4 ≤ 2 * n + 1 := by omega
                  have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                  have h_dvd : 17 ∣ 2 * n + 1 - 2^4 := by
                    apply dvd_of_mod_eq (2 * n + 1) 4 17
                    · change (2 * n + 1) % 17 = 16
                      omega
                    · exact hk
                  have h_gt : 17 < 2 * n + 1 - 2^4 := by omega
                  have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                  have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                    exact composite_of_dvd (2 * n + 1) 4 17 hp17 h_dvd h_gt h1
                  exact A282459_pos_of_exists n 4 h_in h_comp
              · -- Case (2*n+1) % 29 = 1
                have hk : 2^28 ≤ 2 * n + 1 := by omega
                have h_in : 28 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 28 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^28 := by
                  apply dvd_of_mod_eq (2 * n + 1) 28 29
                  · change (2 * n + 1) % 29 = 1
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^28 := by omega
                have h1 : 1 < 2 * n + 1 - 2^28 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^28 ∧ ¬ Nat.Prime (2 * n + 1 - 2^28) := by
                  exact composite_of_dvd (2 * n + 1) 28 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 28 h_in h_comp
              · -- Case (2*n+1) % 29 = 2
                have hk : 2^1 ≤ 2 * n + 1 := by omega
                have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^1 := by
                  apply dvd_of_mod_eq (2 * n + 1) 1 29
                  · change (2 * n + 1) % 29 = 2
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^1 := by omega
                have h1 : 1 < 2 * n + 1 - 2^1 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                  exact composite_of_dvd (2 * n + 1) 1 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 1 h_in h_comp
              · -- Case (2*n+1) % 29 = 3
                have hk : 2^5 ≤ 2 * n + 1 := by omega
                have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^5 := by
                  apply dvd_of_mod_eq (2 * n + 1) 5 29
                  · change (2 * n + 1) % 29 = 3
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^5 := by omega
                have h1 : 1 < 2 * n + 1 - 2^5 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                  exact composite_of_dvd (2 * n + 1) 5 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 5 h_in h_comp
              · -- Case (2*n+1) % 29 = 4
                have hk : 2^2 ≤ 2 * n + 1 := by omega
                have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^2 := by
                  apply dvd_of_mod_eq (2 * n + 1) 2 29
                  · change (2 * n + 1) % 29 = 4
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^2 := by omega
                have h1 : 1 < 2 * n + 1 - 2^2 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                  exact composite_of_dvd (2 * n + 1) 2 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 2 h_in h_comp
              · -- Case (2*n+1) % 29 = 5
                have hk : 2^22 ≤ 2 * n + 1 := by omega
                have h_in : 22 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 22 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^22 := by
                  apply dvd_of_mod_eq (2 * n + 1) 22 29
                  · change (2 * n + 1) % 29 = 5
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^22 := by omega
                have h1 : 1 < 2 * n + 1 - 2^22 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^22 ∧ ¬ Nat.Prime (2 * n + 1 - 2^22) := by
                  exact composite_of_dvd (2 * n + 1) 22 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 22 h_in h_comp
              · -- Case (2*n+1) % 29 = 6
                have hk : 2^6 ≤ 2 * n + 1 := by omega
                have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^6 := by
                  apply dvd_of_mod_eq (2 * n + 1) 6 29
                  · change (2 * n + 1) % 29 = 6
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^6 := by omega
                have h1 : 1 < 2 * n + 1 - 2^6 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                  exact composite_of_dvd (2 * n + 1) 6 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 6 h_in h_comp
              · -- Case (2*n+1) % 29 = 7
                have hk : 2^12 ≤ 2 * n + 1 := by omega
                have h_in : 12 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 12 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^12 := by
                  apply dvd_of_mod_eq (2 * n + 1) 12 29
                  · change (2 * n + 1) % 29 = 7
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^12 := by omega
                have h1 : 1 < 2 * n + 1 - 2^12 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^12 ∧ ¬ Nat.Prime (2 * n + 1 - 2^12) := by
                  exact composite_of_dvd (2 * n + 1) 12 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 12 h_in h_comp
              · -- Case (2*n+1) % 29 = 8
                have hk : 2^3 ≤ 2 * n + 1 := by omega
                have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^3 := by
                  apply dvd_of_mod_eq (2 * n + 1) 3 29
                  · change (2 * n + 1) % 29 = 8
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^3 := by omega
                have h1 : 1 < 2 * n + 1 - 2^3 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                  exact composite_of_dvd (2 * n + 1) 3 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 3 h_in h_comp
              · -- Case (2*n+1) % 29 = 9
                have hk : 2^10 ≤ 2 * n + 1 := by omega
                have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^10 := by
                  apply dvd_of_mod_eq (2 * n + 1) 10 29
                  · change (2 * n + 1) % 29 = 9
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^10 := by omega
                have h1 : 1 < 2 * n + 1 - 2^10 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                  exact composite_of_dvd (2 * n + 1) 10 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 10 h_in h_comp
              · -- Case (2*n+1) % 29 = 10
                have hk : 2^23 ≤ 2 * n + 1 := by omega
                have h_in : 23 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 23 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^23 := by
                  apply dvd_of_mod_eq (2 * n + 1) 23 29
                  · change (2 * n + 1) % 29 = 10
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^23 := by omega
                have h1 : 1 < 2 * n + 1 - 2^23 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^23 ∧ ¬ Nat.Prime (2 * n + 1 - 2^23) := by
                  exact composite_of_dvd (2 * n + 1) 23 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 23 h_in h_comp
              · -- Case (2*n+1) % 29 = 11
                have hk : 2^25 ≤ 2 * n + 1 := by omega
                have h_in : 25 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 25 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^25 := by
                  apply dvd_of_mod_eq (2 * n + 1) 25 29
                  · change (2 * n + 1) % 29 = 11
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^25 := by omega
                have h1 : 1 < 2 * n + 1 - 2^25 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^25 ∧ ¬ Nat.Prime (2 * n + 1 - 2^25) := by
                  exact composite_of_dvd (2 * n + 1) 25 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 25 h_in h_comp
              · -- Case (2*n+1) % 29 = 12
                have hk : 2^7 ≤ 2 * n + 1 := by omega
                have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^7 := by
                  apply dvd_of_mod_eq (2 * n + 1) 7 29
                  · change (2 * n + 1) % 29 = 12
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^7 := by omega
                have h1 : 1 < 2 * n + 1 - 2^7 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                  exact composite_of_dvd (2 * n + 1) 7 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 7 h_in h_comp
              · -- Case (2*n+1) % 29 = 13
                have hk : 2^18 ≤ 2 * n + 1 := by omega
                have h_in : 18 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 18 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^18 := by
                  apply dvd_of_mod_eq (2 * n + 1) 18 29
                  · change (2 * n + 1) % 29 = 13
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^18 := by omega
                have h1 : 1 < 2 * n + 1 - 2^18 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^18 ∧ ¬ Nat.Prime (2 * n + 1 - 2^18) := by
                  exact composite_of_dvd (2 * n + 1) 18 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 18 h_in h_comp
              · -- Case (2*n+1) % 29 = 14
                have hk : 2^13 ≤ 2 * n + 1 := by omega
                have h_in : 13 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 13 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^13 := by
                  apply dvd_of_mod_eq (2 * n + 1) 13 29
                  · change (2 * n + 1) % 29 = 14
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^13 := by omega
                have h1 : 1 < 2 * n + 1 - 2^13 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^13 ∧ ¬ Nat.Prime (2 * n + 1 - 2^13) := by
                  exact composite_of_dvd (2 * n + 1) 13 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 13 h_in h_comp
              · -- Case (2*n+1) % 29 = 15
                have hk : 2^27 ≤ 2 * n + 1 := by omega
                have h_in : 27 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 27 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^27 := by
                  apply dvd_of_mod_eq (2 * n + 1) 27 29
                  · change (2 * n + 1) % 29 = 15
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^27 := by omega
                have h1 : 1 < 2 * n + 1 - 2^27 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^27 ∧ ¬ Nat.Prime (2 * n + 1 - 2^27) := by
                  exact composite_of_dvd (2 * n + 1) 27 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 27 h_in h_comp
              · -- Case (2*n+1) % 29 = 16
                have hk : 2^4 ≤ 2 * n + 1 := by omega
                have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^4 := by
                  apply dvd_of_mod_eq (2 * n + 1) 4 29
                  · change (2 * n + 1) % 29 = 16
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^4 := by omega
                have h1 : 1 < 2 * n + 1 - 2^4 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                  exact composite_of_dvd (2 * n + 1) 4 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 4 h_in h_comp
              · -- Case (2*n+1) % 29 = 17
                have hk : 2^21 ≤ 2 * n + 1 := by omega
                have h_in : 21 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 21 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^21 := by
                  apply dvd_of_mod_eq (2 * n + 1) 21 29
                  · change (2 * n + 1) % 29 = 17
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^21 := by omega
                have h1 : 1 < 2 * n + 1 - 2^21 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^21 ∧ ¬ Nat.Prime (2 * n + 1 - 2^21) := by
                  exact composite_of_dvd (2 * n + 1) 21 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 21 h_in h_comp
              · -- Case (2*n+1) % 29 = 18
                have hk : 2^11 ≤ 2 * n + 1 := by omega
                have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^11 := by
                  apply dvd_of_mod_eq (2 * n + 1) 11 29
                  · change (2 * n + 1) % 29 = 18
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^11 := by omega
                have h1 : 1 < 2 * n + 1 - 2^11 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                  exact composite_of_dvd (2 * n + 1) 11 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 11 h_in h_comp
              · -- Case (2*n+1) % 29 = 19
                have hk : 2^9 ≤ 2 * n + 1 := by omega
                have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^9 := by
                  apply dvd_of_mod_eq (2 * n + 1) 9 29
                  · change (2 * n + 1) % 29 = 19
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^9 := by omega
                have h1 : 1 < 2 * n + 1 - 2^9 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                  exact composite_of_dvd (2 * n + 1) 9 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 9 h_in h_comp
              · -- Case (2*n+1) % 29 = 20
                have hk : 2^24 ≤ 2 * n + 1 := by omega
                have h_in : 24 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 24 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^24 := by
                  apply dvd_of_mod_eq (2 * n + 1) 24 29
                  · change (2 * n + 1) % 29 = 20
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^24 := by omega
                have h1 : 1 < 2 * n + 1 - 2^24 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^24 ∧ ¬ Nat.Prime (2 * n + 1 - 2^24) := by
                  exact composite_of_dvd (2 * n + 1) 24 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 24 h_in h_comp
              · -- Case (2*n+1) % 29 = 21
                have hk : 2^17 ≤ 2 * n + 1 := by omega
                have h_in : 17 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 17 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^17 := by
                  apply dvd_of_mod_eq (2 * n + 1) 17 29
                  · change (2 * n + 1) % 29 = 21
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^17 := by omega
                have h1 : 1 < 2 * n + 1 - 2^17 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^17 ∧ ¬ Nat.Prime (2 * n + 1 - 2^17) := by
                  exact composite_of_dvd (2 * n + 1) 17 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 17 h_in h_comp
              · -- Case (2*n+1) % 29 = 22
                have hk : 2^26 ≤ 2 * n + 1 := by omega
                have h_in : 26 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 26 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^26 := by
                  apply dvd_of_mod_eq (2 * n + 1) 26 29
                  · change (2 * n + 1) % 29 = 22
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^26 := by omega
                have h1 : 1 < 2 * n + 1 - 2^26 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^26 ∧ ¬ Nat.Prime (2 * n + 1 - 2^26) := by
                  exact composite_of_dvd (2 * n + 1) 26 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 26 h_in h_comp
              · -- Case (2*n+1) % 29 = 23
                have hk : 2^20 ≤ 2 * n + 1 := by omega
                have h_in : 20 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 20 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^20 := by
                  apply dvd_of_mod_eq (2 * n + 1) 20 29
                  · change (2 * n + 1) % 29 = 23
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^20 := by omega
                have h1 : 1 < 2 * n + 1 - 2^20 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^20 ∧ ¬ Nat.Prime (2 * n + 1 - 2^20) := by
                  exact composite_of_dvd (2 * n + 1) 20 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 20 h_in h_comp
              · -- Case (2*n+1) % 29 = 24
                have hk : 2^8 ≤ 2 * n + 1 := by omega
                have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^8 := by
                  apply dvd_of_mod_eq (2 * n + 1) 8 29
                  · change (2 * n + 1) % 29 = 24
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^8 := by omega
                have h1 : 1 < 2 * n + 1 - 2^8 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                  exact composite_of_dvd (2 * n + 1) 8 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 8 h_in h_comp
              · -- Case (2*n+1) % 29 = 25
                have hk : 2^16 ≤ 2 * n + 1 := by omega
                have h_in : 16 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 16 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^16 := by
                  apply dvd_of_mod_eq (2 * n + 1) 16 29
                  · change (2 * n + 1) % 29 = 25
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^16 := by omega
                have h1 : 1 < 2 * n + 1 - 2^16 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^16 ∧ ¬ Nat.Prime (2 * n + 1 - 2^16) := by
                  exact composite_of_dvd (2 * n + 1) 16 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 16 h_in h_comp
              · -- Case (2*n+1) % 29 = 26
                have hk : 2^19 ≤ 2 * n + 1 := by omega
                have h_in : 19 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 19 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^19 := by
                  apply dvd_of_mod_eq (2 * n + 1) 19 29
                  · change (2 * n + 1) % 29 = 26
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^19 := by omega
                have h1 : 1 < 2 * n + 1 - 2^19 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^19 ∧ ¬ Nat.Prime (2 * n + 1 - 2^19) := by
                  exact composite_of_dvd (2 * n + 1) 19 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 19 h_in h_comp
              · -- Case (2*n+1) % 29 = 27
                have hk : 2^15 ≤ 2 * n + 1 := by omega
                have h_in : 15 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 15 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^15 := by
                  apply dvd_of_mod_eq (2 * n + 1) 15 29
                  · change (2 * n + 1) % 29 = 27
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^15 := by omega
                have h1 : 1 < 2 * n + 1 - 2^15 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^15 ∧ ¬ Nat.Prime (2 * n + 1 - 2^15) := by
                  exact composite_of_dvd (2 * n + 1) 15 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 15 h_in h_comp
              · -- Case (2*n+1) % 29 = 28
                have hk : 2^14 ≤ 2 * n + 1 := by omega
                have h_in : 14 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 14 (by decide) hk
                have h_dvd : 29 ∣ 2 * n + 1 - 2^14 := by
                  apply dvd_of_mod_eq (2 * n + 1) 14 29
                  · change (2 * n + 1) % 29 = 28
                    omega
                  · exact hk
                have h_gt : 29 < 2 * n + 1 - 2^14 := by omega
                have h1 : 1 < 2 * n + 1 - 2^14 := by omega
                have h_comp : 1 < 2 * n + 1 - 2^14 ∧ ¬ Nat.Prime (2 * n + 1 - 2^14) := by
                  exact composite_of_dvd (2 * n + 1) 14 29 hp29 h_dvd h_gt h1
                exact A282459_pos_of_exists n 14 h_in h_comp
            · -- Case (2*n+1) % 19 = 1
              have hk : 2^18 ≤ 2 * n + 1 := by omega
              have h_in : 18 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 18 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^18 := by
                apply dvd_of_mod_eq (2 * n + 1) 18 19
                · change (2 * n + 1) % 19 = 1
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^18 := by omega
              have h1 : 1 < 2 * n + 1 - 2^18 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^18 ∧ ¬ Nat.Prime (2 * n + 1 - 2^18) := by
                exact composite_of_dvd (2 * n + 1) 18 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 18 h_in h_comp
            · -- Case (2*n+1) % 19 = 2
              have hk : 2^1 ≤ 2 * n + 1 := by omega
              have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^1 := by
                apply dvd_of_mod_eq (2 * n + 1) 1 19
                · change (2 * n + 1) % 19 = 2
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^1 := by omega
              have h1 : 1 < 2 * n + 1 - 2^1 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
                exact composite_of_dvd (2 * n + 1) 1 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 1 h_in h_comp
            · -- Case (2*n+1) % 19 = 3
              have hk : 2^13 ≤ 2 * n + 1 := by omega
              have h_in : 13 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 13 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^13 := by
                apply dvd_of_mod_eq (2 * n + 1) 13 19
                · change (2 * n + 1) % 19 = 3
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^13 := by omega
              have h1 : 1 < 2 * n + 1 - 2^13 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^13 ∧ ¬ Nat.Prime (2 * n + 1 - 2^13) := by
                exact composite_of_dvd (2 * n + 1) 13 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 13 h_in h_comp
            · -- Case (2*n+1) % 19 = 4
              have hk : 2^2 ≤ 2 * n + 1 := by omega
              have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^2 := by
                apply dvd_of_mod_eq (2 * n + 1) 2 19
                · change (2 * n + 1) % 19 = 4
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^2 := by omega
              have h1 : 1 < 2 * n + 1 - 2^2 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
                exact composite_of_dvd (2 * n + 1) 2 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 2 h_in h_comp
            · -- Case (2*n+1) % 19 = 5
              have hk : 2^16 ≤ 2 * n + 1 := by omega
              have h_in : 16 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 16 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^16 := by
                apply dvd_of_mod_eq (2 * n + 1) 16 19
                · change (2 * n + 1) % 19 = 5
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^16 := by omega
              have h1 : 1 < 2 * n + 1 - 2^16 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^16 ∧ ¬ Nat.Prime (2 * n + 1 - 2^16) := by
                exact composite_of_dvd (2 * n + 1) 16 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 16 h_in h_comp
            · -- Case (2*n+1) % 19 = 6
              have hk : 2^14 ≤ 2 * n + 1 := by omega
              have h_in : 14 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 14 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^14 := by
                apply dvd_of_mod_eq (2 * n + 1) 14 19
                · change (2 * n + 1) % 19 = 6
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^14 := by omega
              have h1 : 1 < 2 * n + 1 - 2^14 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^14 ∧ ¬ Nat.Prime (2 * n + 1 - 2^14) := by
                exact composite_of_dvd (2 * n + 1) 14 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 14 h_in h_comp
            · -- Case (2*n+1) % 19 = 7
              have hk : 2^6 ≤ 2 * n + 1 := by omega
              have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^6 := by
                apply dvd_of_mod_eq (2 * n + 1) 6 19
                · change (2 * n + 1) % 19 = 7
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^6 := by omega
              have h1 : 1 < 2 * n + 1 - 2^6 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
                exact composite_of_dvd (2 * n + 1) 6 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 6 h_in h_comp
            · -- Case (2*n+1) % 19 = 8
              have hk : 2^3 ≤ 2 * n + 1 := by omega
              have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^3 := by
                apply dvd_of_mod_eq (2 * n + 1) 3 19
                · change (2 * n + 1) % 19 = 8
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^3 := by omega
              have h1 : 1 < 2 * n + 1 - 2^3 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
                exact composite_of_dvd (2 * n + 1) 3 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 3 h_in h_comp
            · -- Case (2*n+1) % 19 = 9
              have hk : 2^8 ≤ 2 * n + 1 := by omega
              have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^8 := by
                apply dvd_of_mod_eq (2 * n + 1) 8 19
                · change (2 * n + 1) % 19 = 9
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^8 := by omega
              have h1 : 1 < 2 * n + 1 - 2^8 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
                exact composite_of_dvd (2 * n + 1) 8 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 8 h_in h_comp
            · -- Case (2*n+1) % 19 = 10
              have hk : 2^17 ≤ 2 * n + 1 := by omega
              have h_in : 17 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 17 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^17 := by
                apply dvd_of_mod_eq (2 * n + 1) 17 19
                · change (2 * n + 1) % 19 = 10
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^17 := by omega
              have h1 : 1 < 2 * n + 1 - 2^17 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^17 ∧ ¬ Nat.Prime (2 * n + 1 - 2^17) := by
                exact composite_of_dvd (2 * n + 1) 17 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 17 h_in h_comp
            · -- Case (2*n+1) % 19 = 11
              have hk : 2^12 ≤ 2 * n + 1 := by omega
              have h_in : 12 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 12 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^12 := by
                apply dvd_of_mod_eq (2 * n + 1) 12 19
                · change (2 * n + 1) % 19 = 11
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^12 := by omega
              have h1 : 1 < 2 * n + 1 - 2^12 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^12 ∧ ¬ Nat.Prime (2 * n + 1 - 2^12) := by
                exact composite_of_dvd (2 * n + 1) 12 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 12 h_in h_comp
            · -- Case (2*n+1) % 19 = 12
              have hk : 2^15 ≤ 2 * n + 1 := by omega
              have h_in : 15 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 15 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^15 := by
                apply dvd_of_mod_eq (2 * n + 1) 15 19
                · change (2 * n + 1) % 19 = 12
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^15 := by omega
              have h1 : 1 < 2 * n + 1 - 2^15 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^15 ∧ ¬ Nat.Prime (2 * n + 1 - 2^15) := by
                exact composite_of_dvd (2 * n + 1) 15 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 15 h_in h_comp
            · -- Case (2*n+1) % 19 = 13
              have hk : 2^5 ≤ 2 * n + 1 := by omega
              have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^5 := by
                apply dvd_of_mod_eq (2 * n + 1) 5 19
                · change (2 * n + 1) % 19 = 13
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^5 := by omega
              have h1 : 1 < 2 * n + 1 - 2^5 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
                exact composite_of_dvd (2 * n + 1) 5 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 5 h_in h_comp
            · -- Case (2*n+1) % 19 = 14
              have hk : 2^7 ≤ 2 * n + 1 := by omega
              have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^7 := by
                apply dvd_of_mod_eq (2 * n + 1) 7 19
                · change (2 * n + 1) % 19 = 14
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^7 := by omega
              have h1 : 1 < 2 * n + 1 - 2^7 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
                exact composite_of_dvd (2 * n + 1) 7 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 7 h_in h_comp
            · -- Case (2*n+1) % 19 = 15
              have hk : 2^11 ≤ 2 * n + 1 := by omega
              have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^11 := by
                apply dvd_of_mod_eq (2 * n + 1) 11 19
                · change (2 * n + 1) % 19 = 15
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^11 := by omega
              have h1 : 1 < 2 * n + 1 - 2^11 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
                exact composite_of_dvd (2 * n + 1) 11 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 11 h_in h_comp
            · -- Case (2*n+1) % 19 = 16
              have hk : 2^4 ≤ 2 * n + 1 := by omega
              have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^4 := by
                apply dvd_of_mod_eq (2 * n + 1) 4 19
                · change (2 * n + 1) % 19 = 16
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^4 := by omega
              have h1 : 1 < 2 * n + 1 - 2^4 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
                exact composite_of_dvd (2 * n + 1) 4 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 4 h_in h_comp
            · -- Case (2*n+1) % 19 = 17
              have hk : 2^10 ≤ 2 * n + 1 := by omega
              have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^10 := by
                apply dvd_of_mod_eq (2 * n + 1) 10 19
                · change (2 * n + 1) % 19 = 17
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^10 := by omega
              have h1 : 1 < 2 * n + 1 - 2^10 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
                exact composite_of_dvd (2 * n + 1) 10 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 10 h_in h_comp
            · -- Case (2*n+1) % 19 = 18
              have hk : 2^9 ≤ 2 * n + 1 := by omega
              have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
              have h_dvd : 19 ∣ 2 * n + 1 - 2^9 := by
                apply dvd_of_mod_eq (2 * n + 1) 9 19
                · change (2 * n + 1) % 19 = 18
                  omega
                · exact hk
              have h_gt : 19 < 2 * n + 1 - 2^9 := by omega
              have h1 : 1 < 2 * n + 1 - 2^9 := by omega
              have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
                exact composite_of_dvd (2 * n + 1) 9 19 hp19 h_dvd h_gt h1
              exact A282459_pos_of_exists n 9 h_in h_comp
          · -- Case (2*n+1) % 13 = 1
            have hk : 2^12 ≤ 2 * n + 1 := by omega
            have h_in : 12 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 12 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^12 := by
              apply dvd_of_mod_eq (2 * n + 1) 12 13
              · change (2 * n + 1) % 13 = 1
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^12 := by omega
            have h1 : 1 < 2 * n + 1 - 2^12 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^12 ∧ ¬ Nat.Prime (2 * n + 1 - 2^12) := by
              exact composite_of_dvd (2 * n + 1) 12 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 12 h_in h_comp
          · -- Case (2*n+1) % 13 = 2
            have hk : 2^1 ≤ 2 * n + 1 := by omega
            have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^1 := by
              apply dvd_of_mod_eq (2 * n + 1) 1 13
              · change (2 * n + 1) % 13 = 2
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^1 := by omega
            have h1 : 1 < 2 * n + 1 - 2^1 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
              exact composite_of_dvd (2 * n + 1) 1 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 1 h_in h_comp
          · -- Case (2*n+1) % 13 = 3
            have hk : 2^4 ≤ 2 * n + 1 := by omega
            have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^4 := by
              apply dvd_of_mod_eq (2 * n + 1) 4 13
              · change (2 * n + 1) % 13 = 3
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^4 := by omega
            have h1 : 1 < 2 * n + 1 - 2^4 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
              exact composite_of_dvd (2 * n + 1) 4 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 4 h_in h_comp
          · -- Case (2*n+1) % 13 = 4
            have hk : 2^2 ≤ 2 * n + 1 := by omega
            have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^2 := by
              apply dvd_of_mod_eq (2 * n + 1) 2 13
              · change (2 * n + 1) % 13 = 4
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^2 := by omega
            have h1 : 1 < 2 * n + 1 - 2^2 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
              exact composite_of_dvd (2 * n + 1) 2 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 2 h_in h_comp
          · -- Case (2*n+1) % 13 = 5
            have hk : 2^9 ≤ 2 * n + 1 := by omega
            have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^9 := by
              apply dvd_of_mod_eq (2 * n + 1) 9 13
              · change (2 * n + 1) % 13 = 5
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^9 := by omega
            have h1 : 1 < 2 * n + 1 - 2^9 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
              exact composite_of_dvd (2 * n + 1) 9 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 9 h_in h_comp
          · -- Case (2*n+1) % 13 = 6
            have hk : 2^5 ≤ 2 * n + 1 := by omega
            have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^5 := by
              apply dvd_of_mod_eq (2 * n + 1) 5 13
              · change (2 * n + 1) % 13 = 6
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^5 := by omega
            have h1 : 1 < 2 * n + 1 - 2^5 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
              exact composite_of_dvd (2 * n + 1) 5 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 5 h_in h_comp
          · -- Case (2*n+1) % 13 = 7
            have hk : 2^11 ≤ 2 * n + 1 := by omega
            have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^11 := by
              apply dvd_of_mod_eq (2 * n + 1) 11 13
              · change (2 * n + 1) % 13 = 7
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^11 := by omega
            have h1 : 1 < 2 * n + 1 - 2^11 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2^11) := by
              exact composite_of_dvd (2 * n + 1) 11 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 11 h_in h_comp
          · -- Case (2*n+1) % 13 = 8
            have hk : 2^3 ≤ 2 * n + 1 := by omega
            have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^3 := by
              apply dvd_of_mod_eq (2 * n + 1) 3 13
              · change (2 * n + 1) % 13 = 8
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^3 := by omega
            have h1 : 1 < 2 * n + 1 - 2^3 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
              exact composite_of_dvd (2 * n + 1) 3 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 3 h_in h_comp
          · -- Case (2*n+1) % 13 = 9
            have hk : 2^8 ≤ 2 * n + 1 := by omega
            have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^8 := by
              apply dvd_of_mod_eq (2 * n + 1) 8 13
              · change (2 * n + 1) % 13 = 9
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^8 := by omega
            have h1 : 1 < 2 * n + 1 - 2^8 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
              exact composite_of_dvd (2 * n + 1) 8 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 8 h_in h_comp
          · -- Case (2*n+1) % 13 = 10
            have hk : 2^10 ≤ 2 * n + 1 := by omega
            have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^10 := by
              apply dvd_of_mod_eq (2 * n + 1) 10 13
              · change (2 * n + 1) % 13 = 10
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^10 := by omega
            have h1 : 1 < 2 * n + 1 - 2^10 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
              exact composite_of_dvd (2 * n + 1) 10 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 10 h_in h_comp
          · -- Case (2*n+1) % 13 = 11
            have hk : 2^7 ≤ 2 * n + 1 := by omega
            have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^7 := by
              apply dvd_of_mod_eq (2 * n + 1) 7 13
              · change (2 * n + 1) % 13 = 11
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^7 := by omega
            have h1 : 1 < 2 * n + 1 - 2^7 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
              exact composite_of_dvd (2 * n + 1) 7 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 7 h_in h_comp
          · -- Case (2*n+1) % 13 = 12
            have hk : 2^6 ≤ 2 * n + 1 := by omega
            have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
            have h_dvd : 13 ∣ 2 * n + 1 - 2^6 := by
              apply dvd_of_mod_eq (2 * n + 1) 6 13
              · change (2 * n + 1) % 13 = 12
                omega
              · exact hk
            have h_gt : 13 < 2 * n + 1 - 2^6 := by omega
            have h1 : 1 < 2 * n + 1 - 2^6 := by omega
            have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
              exact composite_of_dvd (2 * n + 1) 6 13 hp13 h_dvd h_gt h1
            exact A282459_pos_of_exists n 6 h_in h_comp
        · -- Case (2*n+1) % 11 = 1
          have hk : 2^10 ≤ 2 * n + 1 := by omega
          have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^10 := by
            apply dvd_of_mod_eq (2 * n + 1) 10 11
            · change (2 * n + 1) % 11 = 1
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^10 := by omega
          have h1 : 1 < 2 * n + 1 - 2^10 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2^10) := by
            exact composite_of_dvd (2 * n + 1) 10 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 10 h_in h_comp
        · -- Case (2*n+1) % 11 = 2
          have hk : 2^1 ≤ 2 * n + 1 := by omega
          have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^1 := by
            apply dvd_of_mod_eq (2 * n + 1) 1 11
            · change (2 * n + 1) % 11 = 2
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^1 := by omega
          have h1 : 1 < 2 * n + 1 - 2^1 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
            exact composite_of_dvd (2 * n + 1) 1 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 1 h_in h_comp
        · -- Case (2*n+1) % 11 = 3
          have hk : 2^8 ≤ 2 * n + 1 := by omega
          have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^8 := by
            apply dvd_of_mod_eq (2 * n + 1) 8 11
            · change (2 * n + 1) % 11 = 3
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^8 := by omega
          have h1 : 1 < 2 * n + 1 - 2^8 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2^8) := by
            exact composite_of_dvd (2 * n + 1) 8 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 8 h_in h_comp
        · -- Case (2*n+1) % 11 = 4
          have hk : 2^2 ≤ 2 * n + 1 := by omega
          have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^2 := by
            apply dvd_of_mod_eq (2 * n + 1) 2 11
            · change (2 * n + 1) % 11 = 4
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^2 := by omega
          have h1 : 1 < 2 * n + 1 - 2^2 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
            exact composite_of_dvd (2 * n + 1) 2 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 2 h_in h_comp
        · -- Case (2*n+1) % 11 = 5
          have hk : 2^4 ≤ 2 * n + 1 := by omega
          have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^4 := by
            apply dvd_of_mod_eq (2 * n + 1) 4 11
            · change (2 * n + 1) % 11 = 5
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^4 := by omega
          have h1 : 1 < 2 * n + 1 - 2^4 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
            exact composite_of_dvd (2 * n + 1) 4 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 4 h_in h_comp
        · -- Case (2*n+1) % 11 = 6
          have hk : 2^9 ≤ 2 * n + 1 := by omega
          have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^9 := by
            apply dvd_of_mod_eq (2 * n + 1) 9 11
            · change (2 * n + 1) % 11 = 6
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^9 := by omega
          have h1 : 1 < 2 * n + 1 - 2^9 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2^9) := by
            exact composite_of_dvd (2 * n + 1) 9 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 9 h_in h_comp
        · -- Case (2*n+1) % 11 = 7
          have hk : 2^7 ≤ 2 * n + 1 := by omega
          have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^7 := by
            apply dvd_of_mod_eq (2 * n + 1) 7 11
            · change (2 * n + 1) % 11 = 7
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^7 := by omega
          have h1 : 1 < 2 * n + 1 - 2^7 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2^7) := by
            exact composite_of_dvd (2 * n + 1) 7 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 7 h_in h_comp
        · -- Case (2*n+1) % 11 = 8
          have hk : 2^3 ≤ 2 * n + 1 := by omega
          have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^3 := by
            apply dvd_of_mod_eq (2 * n + 1) 3 11
            · change (2 * n + 1) % 11 = 8
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^3 := by omega
          have h1 : 1 < 2 * n + 1 - 2^3 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
            exact composite_of_dvd (2 * n + 1) 3 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 3 h_in h_comp
        · -- Case (2*n+1) % 11 = 9
          have hk : 2^6 ≤ 2 * n + 1 := by omega
          have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^6 := by
            apply dvd_of_mod_eq (2 * n + 1) 6 11
            · change (2 * n + 1) % 11 = 9
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^6 := by omega
          have h1 : 1 < 2 * n + 1 - 2^6 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2^6) := by
            exact composite_of_dvd (2 * n + 1) 6 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 6 h_in h_comp
        · -- Case (2*n+1) % 11 = 10
          have hk : 2^5 ≤ 2 * n + 1 := by omega
          have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
          have h_dvd : 11 ∣ 2 * n + 1 - 2^5 := by
            apply dvd_of_mod_eq (2 * n + 1) 5 11
            · change (2 * n + 1) % 11 = 10
              omega
            · exact hk
          have h_gt : 11 < 2 * n + 1 - 2^5 := by omega
          have h1 : 1 < 2 * n + 1 - 2^5 := by omega
          have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2^5) := by
            exact composite_of_dvd (2 * n + 1) 5 11 hp11 h_dvd h_gt h1
          exact A282459_pos_of_exists n 5 h_in h_comp
      · -- Case (2*n+1) % 5 = 1
        have hk : 2^4 ≤ 2 * n + 1 := by omega
        have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
        have h_dvd : 5 ∣ 2 * n + 1 - 2^4 := by
          apply dvd_of_mod_eq (2 * n + 1) 4 5
          · change (2 * n + 1) % 5 = 1
            omega
          · exact hk
        have h_gt : 5 < 2 * n + 1 - 2^4 := by omega
        have h1 : 1 < 2 * n + 1 - 2^4 := by omega
        have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2^4) := by
          exact composite_of_dvd (2 * n + 1) 4 5 hp5 h_dvd h_gt h1
        exact A282459_pos_of_exists n 4 h_in h_comp
      · -- Case (2*n+1) % 5 = 2
        have hk : 2^1 ≤ 2 * n + 1 := by omega
        have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
        have h_dvd : 5 ∣ 2 * n + 1 - 2^1 := by
          apply dvd_of_mod_eq (2 * n + 1) 1 5
          · change (2 * n + 1) % 5 = 2
            omega
          · exact hk
        have h_gt : 5 < 2 * n + 1 - 2^1 := by omega
        have h1 : 1 < 2 * n + 1 - 2^1 := by omega
        have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
          exact composite_of_dvd (2 * n + 1) 1 5 hp5 h_dvd h_gt h1
        exact A282459_pos_of_exists n 1 h_in h_comp
      · -- Case (2*n+1) % 5 = 3
        have hk : 2^3 ≤ 2 * n + 1 := by omega
        have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
        have h_dvd : 5 ∣ 2 * n + 1 - 2^3 := by
          apply dvd_of_mod_eq (2 * n + 1) 3 5
          · change (2 * n + 1) % 5 = 3
            omega
          · exact hk
        have h_gt : 5 < 2 * n + 1 - 2^3 := by omega
        have h1 : 1 < 2 * n + 1 - 2^3 := by omega
        have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2^3) := by
          exact composite_of_dvd (2 * n + 1) 3 5 hp5 h_dvd h_gt h1
        exact A282459_pos_of_exists n 3 h_in h_comp
      · -- Case (2*n+1) % 5 = 4
        have hk : 2^2 ≤ 2 * n + 1 := by omega
        have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
        have h_dvd : 5 ∣ 2 * n + 1 - 2^2 := by
          apply dvd_of_mod_eq (2 * n + 1) 2 5
          · change (2 * n + 1) % 5 = 4
            omega
          · exact hk
        have h_gt : 5 < 2 * n + 1 - 2^2 := by omega
        have h1 : 1 < 2 * n + 1 - 2^2 := by omega
        have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
          exact composite_of_dvd (2 * n + 1) 2 5 hp5 h_dvd h_gt h1
        exact A282459_pos_of_exists n 2 h_in h_comp
    · -- Case (2*n+1) % 3 = 1
      have hk : 2^2 ≤ 2 * n + 1 := by omega
      have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
      have h_dvd : 3 ∣ 2 * n + 1 - 2^2 := by
        apply dvd_of_mod_eq (2 * n + 1) 2 3
        · change (2 * n + 1) % 3 = 1
          omega
        · exact hk
      have h_gt : 3 < 2 * n + 1 - 2^2 := by omega
      have h1 : 1 < 2 * n + 1 - 2^2 := by omega
      have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2^2) := by
        exact composite_of_dvd (2 * n + 1) 2 3 hp3 h_dvd h_gt h1
      exact A282459_pos_of_exists n 2 h_in h_comp
    · -- Case (2*n+1) % 3 = 2
      have hk : 2^1 ≤ 2 * n + 1 := by omega
      have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
      have h_dvd : 3 ∣ 2 * n + 1 - 2^1 := by
        apply dvd_of_mod_eq (2 * n + 1) 1 3
        · change (2 * n + 1) % 3 = 2
          omega
        · exact hk
      have h_gt : 3 < 2 * n + 1 - 2^1 := by omega
      have h1 : 1 < 2 * n + 1 - 2^1 := by omega
      have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2^1) := by
        exact composite_of_dvd (2 * n + 1) 1 3 hp3 h_dvd h_gt h1
      exact A282459_pos_of_exists n 1 h_in h_comp
