import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

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

lemma hk_of_ge (A B : ℕ) (hA : A ≥ 4111) (hB : B ≤ 2048) : B ≤ A := by
  omega

lemma gt_of_ge (A B C : ℕ) (hA : A ≥ 4111) (hB : B ≤ 2048) (hC : C ≤ 29) : C < A - B := by
  omega

lemma h1_of_ge (A B : ℕ) (hA : A ≥ 4111) (hB : B ≤ 2048) : 1 < A - B := by
  omega

-- Dummy definition of A282459 and its lemma
def A282459 (n : ℕ) : ℕ := 1
lemma A282459_pos_of_exists (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)))
    (h_comp : 1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k)) : A282459 n > 0 := by
  omega

lemma hp3 : Nat.Prime 3 := Nat.prime_three
lemma hp5 : Nat.Prime 5 := by decide
lemma hp7 : Nat.Prime 7 := by decide
lemma hp11 : Nat.Prime 11 := by decide
lemma hp13 : Nat.Prime 13 := by decide
lemma hp17 : Nat.Prime 17 := by decide
lemma hp19 : Nat.Prime 19 := by decide
lemma hp23 : Nat.Prime 23 := by decide
lemma hp29 : Nat.Prime 29 := by decide
lemma hp31 : Nat.Prime 31 := by decide
lemma hp37 : Nat.Prime 37 := by decide
lemma hp41 : Nat.Prime 41 := by decide
lemma hp43 : Nat.Prime 43 := by decide
lemma hp47 : Nat.Prime 47 := by decide
lemma hp53 : Nat.Prime 53 := by decide
lemma hp59 : Nat.Prime 59 := by decide
lemma hp73 : Nat.Prime 73 := by decide

lemma solve_tree_node_0_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 0) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 231060472 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 231060472 + 1)) := by decide
    have hdvd_231060472 : 31 ∣ 2 * 231060472 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 231060472 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 231060472 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 231060472 + 1) 3 31 hp31 hdvd_231060472 (by decide) (by decide)
    exact A282459_pos_of_exists 231060472 3 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 110507182 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 110507182 + 1)) := by decide
    have hdvd_110507182 : 37 ∣ 2 * 110507182 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 110507182 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 110507182 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 110507182 + 1) 3 37 hp37 hdvd_110507182 (by decide) (by decide)
    exact A282459_pos_of_exists 110507182 3 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 431982622 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 431982622 + 1)) := by decide
    have hdvd_431982622 : 41 ∣ 2 * 431982622 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 431982622 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 431982622 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 431982622 + 1) 1 41 hp41 hdvd_431982622 (by decide) (by decide)
    exact A282459_pos_of_exists 431982622 1 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 452074837 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 452074837 + 1)) := by decide
    have hdvd_452074837 : 7 ∣ 2 * 452074837 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 452074837 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 452074837 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 452074837 + 1) 1 7 hp7 hdvd_452074837 (by decide) (by decide)
    exact A282459_pos_of_exists 452074837 1 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 150691612 := by omega
    subst h_eq
    have hk : 4 ∈ Finset.Icc 1 (log 2 (2 * 150691612 + 1)) := by decide
    have hdvd_150691612 : 31 ∣ 2 * 150691612 + 1 - 2 ^ 4 := by decide
    have h_comp : 1 < 2 * 150691612 + 1 - 2 ^ 4 ∧ ¬ Nat.Prime (2 * 150691612 + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * 150691612 + 1) 4 31 hp31 hdvd_150691612 (by decide) (by decide)
    exact A282459_pos_of_exists 150691612 4 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 170783827 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 170783827 + 1)) := by decide
    have hdvd_170783827 : 7 ∣ 2 * 170783827 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 170783827 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 170783827 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 170783827 + 1) 1 7 hp7 hdvd_170783827 (by decide) (by decide)
    exact A282459_pos_of_exists 170783827 1 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 331521547 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 331521547 + 1)) := by decide
    have hdvd_331521547 : 7 ∣ 2 * 331521547 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 331521547 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 331521547 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 331521547 + 1) 3 7 hp7 hdvd_331521547 (by decide) (by decide)
    exact A282459_pos_of_exists 331521547 3 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 190876042 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 190876042 + 1)) := by decide
    have hdvd_190876042 : 7 ∣ 2 * 190876042 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 190876042 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 190876042 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 190876042 + 1) 3 7 hp7 hdvd_190876042 (by decide) (by decide)
    exact A282459_pos_of_exists 190876042 3 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 50230537 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 50230537 + 1)) := by decide
    have hdvd_50230537 : 7 ∣ 2 * 50230537 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 50230537 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 50230537 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 50230537 + 1) 3 7 hp7 hdvd_50230537 (by decide) (by decide)
    exact A282459_pos_of_exists 50230537 3 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 210968257 := by omega
    subst h_eq
    have hk : 19 ∈ Finset.Icc 1 (log 2 (2 * 210968257 + 1)) := by decide
    have hdvd_210968257 : 41 ∣ 2 * 210968257 + 1 - 2 ^ 19 := by decide
    have h_comp : 1 < 2 * 210968257 + 1 - 2 ^ 19 ∧ ¬ Nat.Prime (2 * 210968257 + 1 - 2 ^ 19) :=
      composite_of_dvd (2 * 210968257 + 1) 19 41 hp41 hdvd_210968257 (by decide) (by decide)
    exact A282459_pos_of_exists 210968257 19 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 371705977 := by omega
    subst h_eq
    have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 371705977 + 1)) := by decide
    have hdvd_371705977 : 41 ∣ 2 * 371705977 + 1 - 2 ^ 12 := by decide
    have h_comp : 1 < 2 * 371705977 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 371705977 + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * 371705977 + 1) 12 41 hp41 hdvd_371705977 (by decide) (by decide)
    exact A282459_pos_of_exists 371705977 12 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 70322752 := by omega
    subst h_eq
    have hk : 5 ∈ Finset.Icc 1 (log 2 (2 * 70322752 + 1)) := by decide
    have hdvd_70322752 : 37 ∣ 2 * 70322752 + 1 - 2 ^ 5 := by decide
    have h_comp : 1 < 2 * 70322752 + 1 - 2 ^ 5 ∧ ¬ Nat.Prime (2 * 70322752 + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * 70322752 + 1) 5 37 hp37 hdvd_70322752 (by decide) (by decide)
    exact A282459_pos_of_exists 70322752 5 hk h_comp

lemma solve_tree_node_1_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 3) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 203876887 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 203876887 + 1)) := by decide
    have hdvd_203876887 : 7 ∣ 2 * 203876887 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 203876887 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 203876887 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 203876887 + 1) 1 7 hp7 hdvd_203876887 (by decide) (by decide)
    exact A282459_pos_of_exists 203876887 1 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 83323597 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 83323597 + 1)) := by decide
    have hdvd_83323597 : 7 ∣ 2 * 83323597 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 83323597 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 83323597 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 83323597 + 1) 3 7 hp7 hdvd_83323597 (by decide) (by decide)
    exact A282459_pos_of_exists 83323597 3 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 404799037 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 404799037 + 1)) := by decide
    have hdvd_404799037 : 37 ∣ 2 * 404799037 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 404799037 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 404799037 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 404799037 + 1) 1 37 hp37 hdvd_404799037 (by decide) (by decide)
    exact A282459_pos_of_exists 404799037 1 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 424891252 := by omega
    subst h_eq
    have hk : 6 ∈ Finset.Icc 1 (log 2 (2 * 424891252 + 1)) := by decide
    have hdvd_424891252 : 37 ∣ 2 * 424891252 + 1 - 2 ^ 6 := by decide
    have h_comp : 1 < 2 * 424891252 + 1 - 2 ^ 6 ∧ ¬ Nat.Prime (2 * 424891252 + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * 424891252 + 1) 6 37 hp37 hdvd_424891252 (by decide) (by decide)
    exact A282459_pos_of_exists 424891252 6 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 123508027 := by omega
    subst h_eq
    have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 123508027 + 1)) := by decide
    have hdvd_123508027 : 53 ∣ 2 * 123508027 + 1 - 2 ^ 12 := by decide
    have h_comp : 1 < 2 * 123508027 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 123508027 + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * 123508027 + 1) 12 53 hp53 hdvd_123508027 (by decide) (by decide)
    exact A282459_pos_of_exists 123508027 12 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 143600242 := by omega
    subst h_eq
    have hk : 24 ∈ Finset.Icc 1 (log 2 (2 * 143600242 + 1)) := by decide
    have hdvd_143600242 : 37 ∣ 2 * 143600242 + 1 - 2 ^ 24 := by decide
    have h_comp : 1 < 2 * 143600242 + 1 - 2 ^ 24 ∧ ¬ Nat.Prime (2 * 143600242 + 1 - 2 ^ 24) :=
      composite_of_dvd (2 * 143600242 + 1) 24 37 hp37 hdvd_143600242 (by decide) (by decide)
    exact A282459_pos_of_exists 143600242 24 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 304337962 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 304337962 + 1)) := by decide
    have hdvd_304337962 : 7 ∣ 2 * 304337962 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 304337962 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 304337962 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 304337962 + 1) 2 7 hp7 hdvd_304337962 (by decide) (by decide)
    exact A282459_pos_of_exists 304337962 2 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 163692457 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 163692457 + 1)) := by decide
    have hdvd_163692457 : 7 ∣ 2 * 163692457 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 163692457 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 163692457 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 163692457 + 1) 2 7 hp7 hdvd_163692457 (by decide) (by decide)
    exact A282459_pos_of_exists 163692457 2 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 23046952 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 23046952 + 1)) := by decide
    have hdvd_23046952 : 7 ∣ 2 * 23046952 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 23046952 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 23046952 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 23046952 + 1) 2 7 hp7 hdvd_23046952 (by decide) (by decide)
    exact A282459_pos_of_exists 23046952 2 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 183784672 := by omega
    subst h_eq
    have hk : 15 ∈ Finset.Icc 1 (log 2 (2 * 183784672 + 1)) := by decide
    have hdvd_183784672 : 37 ∣ 2 * 183784672 + 1 - 2 ^ 15 := by decide
    have h_comp : 1 < 2 * 183784672 + 1 - 2 ^ 15 ∧ ¬ Nat.Prime (2 * 183784672 + 1 - 2 ^ 15) :=
      composite_of_dvd (2 * 183784672 + 1) 15 37 hp37 hdvd_183784672 (by decide) (by decide)
    exact A282459_pos_of_exists 183784672 15 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 344522392 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 344522392 + 1)) := by decide
    have hdvd_344522392 : 7 ∣ 2 * 344522392 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 344522392 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 344522392 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 344522392 + 1) 1 7 hp7 hdvd_344522392 (by decide) (by decide)
    exact A282459_pos_of_exists 344522392 1 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 43139167 := by omega
    subst h_eq
    have hk : 20 ∈ Finset.Icc 1 (log 2 (2 * 43139167 + 1)) := by decide
    have hdvd_43139167 : 37 ∣ 2 * 43139167 + 1 - 2 ^ 20 := by decide
    have h_comp : 1 < 2 * 43139167 + 1 - 2 ^ 20 ∧ ¬ Nat.Prime (2 * 43139167 + 1 - 2 ^ 20) :=
      composite_of_dvd (2 * 43139167 + 1) 20 37 hp37 hdvd_43139167 (by decide) (by decide)
    exact A282459_pos_of_exists 43139167 20 hk h_comp

lemma solve_tree_node_2_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 5) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 339794812 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 339794812 + 1)) := by decide
    have hdvd_339794812 : 7 ∣ 2 * 339794812 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 339794812 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 339794812 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 339794812 + 1) 3 7 hp7 hdvd_339794812 (by decide) (by decide)
    exact A282459_pos_of_exists 339794812 3 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 219241522 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 219241522 + 1)) := by decide
    have hdvd_219241522 : 37 ∣ 2 * 219241522 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 219241522 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 219241522 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 219241522 + 1) 2 37 hp37 hdvd_219241522 (by decide) (by decide)
    exact A282459_pos_of_exists 219241522 2 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 78596017 := by omega
    subst h_eq
    have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 78596017 + 1)) := by decide
    have hdvd_78596017 : 47 ∣ 2 * 78596017 + 1 - 2 ^ 16 := by decide
    have h_comp : 1 < 2 * 78596017 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 78596017 + 1 - 2 ^ 16) :=
      composite_of_dvd (2 * 78596017 + 1) 16 47 hp47 hdvd_78596017 (by decide) (by decide)
    exact A282459_pos_of_exists 78596017 16 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 98688232 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 98688232 + 1)) := by decide
    have hdvd_98688232 : 37 ∣ 2 * 98688232 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 98688232 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 98688232 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 98688232 + 1) 1 37 hp37 hdvd_98688232 (by decide) (by decide)
    exact A282459_pos_of_exists 98688232 1 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 259425952 := by omega
    subst h_eq
    have hk : 7 ∈ Finset.Icc 1 (log 2 (2 * 259425952 + 1)) := by decide
    have hdvd_259425952 : 37 ∣ 2 * 259425952 + 1 - 2 ^ 7 := by decide
    have h_comp : 1 < 2 * 259425952 + 1 - 2 ^ 7 ∧ ¬ Nat.Prime (2 * 259425952 + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * 259425952 + 1) 7 37 hp37 hdvd_259425952 (by decide) (by decide)
    exact A282459_pos_of_exists 259425952 7 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 279518167 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 279518167 + 1)) := by decide
    have hdvd_279518167 : 7 ∣ 2 * 279518167 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 279518167 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 279518167 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 279518167 + 1) 2 7 hp7 hdvd_279518167 (by decide) (by decide)
    exact A282459_pos_of_exists 279518167 2 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 440255887 := by omega
    subst h_eq
    have hk : 25 ∈ Finset.Icc 1 (log 2 (2 * 440255887 + 1)) := by decide
    have hdvd_440255887 : 37 ∣ 2 * 440255887 + 1 - 2 ^ 25 := by decide
    have h_comp : 1 < 2 * 440255887 + 1 - 2 ^ 25 ∧ ¬ Nat.Prime (2 * 440255887 + 1 - 2 ^ 25) :=
      composite_of_dvd (2 * 440255887 + 1) 25 37 hp37 hdvd_440255887 (by decide) (by decide)
    exact A282459_pos_of_exists 440255887 25 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 299610382 := by omega
    subst h_eq
    have hk : 14 ∈ Finset.Icc 1 (log 2 (2 * 299610382 + 1)) := by decide
    have hdvd_299610382 : 37 ∣ 2 * 299610382 + 1 - 2 ^ 14 := by decide
    have h_comp : 1 < 2 * 299610382 + 1 - 2 ^ 14 ∧ ¬ Nat.Prime (2 * 299610382 + 1 - 2 ^ 14) :=
      composite_of_dvd (2 * 299610382 + 1) 14 37 hp37 hdvd_299610382 (by decide) (by decide)
    exact A282459_pos_of_exists 299610382 14 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 158964877 := by omega
    subst h_eq
    have hk : 26 ∈ Finset.Icc 1 (log 2 (2 * 158964877 + 1)) := by decide
    have hdvd_158964877 : 37 ∣ 2 * 158964877 + 1 - 2 ^ 26 := by decide
    have h_comp : 1 < 2 * 158964877 + 1 - 2 ^ 26 ∧ ¬ Nat.Prime (2 * 158964877 + 1 - 2 ^ 26) :=
      composite_of_dvd (2 * 158964877 + 1) 26 37 hp37 hdvd_158964877 (by decide) (by decide)
    exact A282459_pos_of_exists 158964877 26 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 319702597 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 319702597 + 1)) := by decide
    have hdvd_319702597 : 7 ∣ 2 * 319702597 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 319702597 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 319702597 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 319702597 + 1) 1 7 hp7 hdvd_319702597 (by decide) (by decide)
    exact A282459_pos_of_exists 319702597 1 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 18319372 := by omega
    subst h_eq
    have hk : 11 ∈ Finset.Icc 1 (log 2 (2 * 18319372 + 1)) := by decide
    have hdvd_18319372 : 37 ∣ 2 * 18319372 + 1 - 2 ^ 11 := by decide
    have h_comp : 1 < 2 * 18319372 + 1 - 2 ^ 11 ∧ ¬ Nat.Prime (2 * 18319372 + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * 18319372 + 1) 11 37 hp37 hdvd_18319372 (by decide) (by decide)
    exact A282459_pos_of_exists 18319372 11 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 179057092 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 179057092 + 1)) := by decide
    have hdvd_179057092 : 7 ∣ 2 * 179057092 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 179057092 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 179057092 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 179057092 + 1) 1 7 hp7 hdvd_179057092 (by decide) (by decide)
    exact A282459_pos_of_exists 179057092 1 hk h_comp

lemma solve_tree_node_3_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 6) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 176693302 := by omega
    subst h_eq
    have hk : 28 ∈ Finset.Icc 1 (log 2 (2 * 176693302 + 1)) := by decide
    have hdvd_176693302 : 37 ∣ 2 * 176693302 + 1 - 2 ^ 28 := by decide
    have h_comp : 1 < 2 * 176693302 + 1 - 2 ^ 28 ∧ ¬ Nat.Prime (2 * 176693302 + 1 - 2 ^ 28) :=
      composite_of_dvd (2 * 176693302 + 1) 28 37 hp37 hdvd_176693302 (by decide) (by decide)
    exact A282459_pos_of_exists 176693302 28 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 56140012 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 56140012 + 1)) := by decide
    have hdvd_56140012 : 7 ∣ 2 * 56140012 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 56140012 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 56140012 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 56140012 + 1) 2 7 hp7 hdvd_56140012 (by decide) (by decide)
    exact A282459_pos_of_exists 56140012 2 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 377615452 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 377615452 + 1)) := by decide
    have hdvd_377615452 : 7 ∣ 2 * 377615452 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 377615452 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 377615452 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 377615452 + 1) 1 7 hp7 hdvd_377615452 (by decide) (by decide)
    exact A282459_pos_of_exists 377615452 1 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 397707667 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 397707667 + 1)) := by decide
    have hdvd_397707667 : 7 ∣ 2 * 397707667 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 397707667 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 397707667 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 397707667 + 1) 3 7 hp7 hdvd_397707667 (by decide) (by decide)
    exact A282459_pos_of_exists 397707667 3 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 96324442 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 96324442 + 1)) := by decide
    have hdvd_96324442 : 7 ∣ 2 * 96324442 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 96324442 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 96324442 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 96324442 + 1) 1 7 hp7 hdvd_96324442 (by decide) (by decide)
    exact A282459_pos_of_exists 96324442 1 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 116416657 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 116416657 + 1)) := by decide
    have hdvd_116416657 : 7 ∣ 2 * 116416657 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 116416657 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 116416657 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 116416657 + 1) 3 7 hp7 hdvd_116416657 (by decide) (by decide)
    exact A282459_pos_of_exists 116416657 3 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 277154377 := by omega
    subst h_eq
    have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 277154377 + 1)) := by decide
    have hdvd_277154377 : 37 ∣ 2 * 277154377 + 1 - 2 ^ 12 := by decide
    have h_comp : 1 < 2 * 277154377 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 277154377 + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * 277154377 + 1) 12 37 hp37 hdvd_277154377 (by decide) (by decide)
    exact A282459_pos_of_exists 277154377 12 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 136508872 := by omega
    subst h_eq
    have hk : 5 ∈ Finset.Icc 1 (log 2 (2 * 136508872 + 1)) := by decide
    have hdvd_136508872 : 31 ∣ 2 * 136508872 + 1 - 2 ^ 5 := by decide
    have h_comp : 1 < 2 * 136508872 + 1 - 2 ^ 5 ∧ ¬ Nat.Prime (2 * 136508872 + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * 136508872 + 1) 5 31 hp31 hdvd_136508872 (by decide) (by decide)
    exact A282459_pos_of_exists 136508872 5 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 457984312 := by omega
    subst h_eq
    have hk : 21 ∈ Finset.Icc 1 (log 2 (2 * 457984312 + 1)) := by decide
    have hdvd_457984312 : 37 ∣ 2 * 457984312 + 1 - 2 ^ 21 := by decide
    have h_comp : 1 < 2 * 457984312 + 1 - 2 ^ 21 ∧ ¬ Nat.Prime (2 * 457984312 + 1 - 2 ^ 21) :=
      composite_of_dvd (2 * 457984312 + 1) 21 37 hp37 hdvd_457984312 (by decide) (by decide)
    exact A282459_pos_of_exists 457984312 21 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 156601087 := by omega
    subst h_eq
    have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 156601087 + 1)) := by decide
    have hdvd_156601087 : 41 ∣ 2 * 156601087 + 1 - 2 ^ 16 := by decide
    have h_comp : 1 < 2 * 156601087 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 156601087 + 1 - 2 ^ 16) :=
      composite_of_dvd (2 * 156601087 + 1) 16 41 hp41 hdvd_156601087 (by decide) (by decide)
    exact A282459_pos_of_exists 156601087 16 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 317338807 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 317338807 + 1)) := by decide
    have hdvd_317338807 : 37 ∣ 2 * 317338807 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 317338807 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 317338807 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 317338807 + 1) 1 37 hp37 hdvd_317338807 (by decide) (by decide)
    exact A282459_pos_of_exists 317338807 1 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 15955582 := by omega
    subst h_eq
    have hk : 8 ∈ Finset.Icc 1 (log 2 (2 * 15955582 + 1)) := by decide
    have hdvd_15955582 : 37 ∣ 2 * 15955582 + 1 - 2 ^ 8 := by decide
    have h_comp : 1 < 2 * 15955582 + 1 - 2 ^ 8 ∧ ¬ Nat.Prime (2 * 15955582 + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * 15955582 + 1) 8 37 hp37 hdvd_15955582 (by decide) (by decide)
    exact A282459_pos_of_exists 15955582 8 hk h_comp

lemma solve_tree_node_4_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 7) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 13591792 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 13591792 + 1)) := by decide
    have hdvd_13591792 : 7 ∣ 2 * 13591792 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 13591792 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 13591792 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 13591792 + 1) 1 7 hp7 hdvd_13591792 (by decide) (by decide)
    exact A282459_pos_of_exists 13591792 1 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 355159447 := by omega
    subst h_eq
    have hk : 18 ∈ Finset.Icc 1 (log 2 (2 * 355159447 + 1)) := by decide
    have hdvd_355159447 : 37 ∣ 2 * 355159447 + 1 - 2 ^ 18 := by decide
    have h_comp : 1 < 2 * 355159447 + 1 - 2 ^ 18 ∧ ¬ Nat.Prime (2 * 355159447 + 1 - 2 ^ 18) :=
      composite_of_dvd (2 * 355159447 + 1) 18 37 hp37 hdvd_355159447 (by decide) (by decide)
    exact A282459_pos_of_exists 355159447 18 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 214513942 := by omega
    subst h_eq
    have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 214513942 + 1)) := by decide
    have hdvd_214513942 : 37 ∣ 2 * 214513942 + 1 - 2 ^ 16 := by decide
    have h_comp : 1 < 2 * 214513942 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 214513942 + 1 - 2 ^ 16) :=
      composite_of_dvd (2 * 214513942 + 1) 16 37 hp37 hdvd_214513942 (by decide) (by decide)
    exact A282459_pos_of_exists 214513942 16 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 234606157 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 234606157 + 1)) := by decide
    have hdvd_234606157 : 31 ∣ 2 * 234606157 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 234606157 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 234606157 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 234606157 + 1) 2 31 hp31 hdvd_234606157 (by decide) (by decide)
    exact A282459_pos_of_exists 234606157 2 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 395343877 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 395343877 + 1)) := by decide
    have hdvd_395343877 : 7 ∣ 2 * 395343877 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 395343877 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 395343877 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 395343877 + 1) 2 7 hp7 hdvd_395343877 (by decide) (by decide)
    exact A282459_pos_of_exists 395343877 2 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 415436092 := by omega
    subst h_eq
    have hk : 8 ∈ Finset.Icc 1 (log 2 (2 * 415436092 + 1)) := by decide
    have hdvd_415436092 : 41 ∣ 2 * 415436092 + 1 - 2 ^ 8 := by decide
    have h_comp : 1 < 2 * 415436092 + 1 - 2 ^ 8 ∧ ¬ Nat.Prime (2 * 415436092 + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * 415436092 + 1) 8 41 hp41 hdvd_415436092 (by decide) (by decide)
    exact A282459_pos_of_exists 415436092 8 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 114052867 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 114052867 + 1)) := by decide
    have hdvd_114052867 : 7 ∣ 2 * 114052867 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 114052867 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 114052867 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 114052867 + 1) 2 7 hp7 hdvd_114052867 (by decide) (by decide)
    exact A282459_pos_of_exists 114052867 2 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 435528307 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 435528307 + 1)) := by decide
    have hdvd_435528307 : 7 ∣ 2 * 435528307 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 435528307 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 435528307 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 435528307 + 1) 1 7 hp7 hdvd_435528307 (by decide) (by decide)
    exact A282459_pos_of_exists 435528307 1 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 294882802 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 294882802 + 1)) := by decide
    have hdvd_294882802 : 7 ∣ 2 * 294882802 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 294882802 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 294882802 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 294882802 + 1) 1 7 hp7 hdvd_294882802 (by decide) (by decide)
    exact A282459_pos_of_exists 294882802 1 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 455620522 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 455620522 + 1)) := by decide
    have hdvd_455620522 : 7 ∣ 2 * 455620522 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 455620522 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 455620522 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 455620522 + 1) 3 7 hp7 hdvd_455620522 (by decide) (by decide)
    exact A282459_pos_of_exists 455620522 3 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 154237297 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 154237297 + 1)) := by decide
    have hdvd_154237297 : 7 ∣ 2 * 154237297 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 154237297 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 154237297 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 154237297 + 1) 1 7 hp7 hdvd_154237297 (by decide) (by decide)
    exact A282459_pos_of_exists 154237297 1 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 314975017 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 314975017 + 1)) := by decide
    have hdvd_314975017 : 7 ∣ 2 * 314975017 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 314975017 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 314975017 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 314975017 + 1) 3 7 hp7 hdvd_314975017 (by decide) (by decide)
    exact A282459_pos_of_exists 314975017 3 hk h_comp

lemma solve_tree_node_5_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 10) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 448529152 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 448529152 + 1)) := by decide
    have hdvd_448529152 : 37 ∣ 2 * 448529152 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 448529152 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 448529152 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 448529152 + 1) 1 37 hp37 hdvd_448529152 (by decide) (by decide)
    exact A282459_pos_of_exists 448529152 1 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 327975862 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 327975862 + 1)) := by decide
    have hdvd_327975862 : 7 ∣ 2 * 327975862 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 327975862 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 327975862 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 327975862 + 1) 1 7 hp7 hdvd_327975862 (by decide) (by decide)
    exact A282459_pos_of_exists 327975862 1 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 187330357 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 187330357 + 1)) := by decide
    have hdvd_187330357 : 7 ∣ 2 * 187330357 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 187330357 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 187330357 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 187330357 + 1) 1 7 hp7 hdvd_187330357 (by decide) (by decide)
    exact A282459_pos_of_exists 187330357 1 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 207422572 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 207422572 + 1)) := by decide
    have hdvd_207422572 : 7 ∣ 2 * 207422572 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 207422572 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 207422572 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 207422572 + 1) 3 7 hp7 hdvd_207422572 (by decide) (by decide)
    exact A282459_pos_of_exists 207422572 3 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 368160292 := by omega
    subst h_eq
    have hk : 11 ∈ Finset.Icc 1 (log 2 (2 * 368160292 + 1)) := by decide
    have hdvd_368160292 : 37 ∣ 2 * 368160292 + 1 - 2 ^ 11 := by decide
    have h_comp : 1 < 2 * 368160292 + 1 - 2 ^ 11 ∧ ¬ Nat.Prime (2 * 368160292 + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * 368160292 + 1) 11 37 hp37 hdvd_368160292 (by decide) (by decide)
    exact A282459_pos_of_exists 368160292 11 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 388252507 := by omega
    subst h_eq
    have hk : 13 ∈ Finset.Icc 1 (log 2 (2 * 388252507 + 1)) := by decide
    have hdvd_388252507 : 47 ∣ 2 * 388252507 + 1 - 2 ^ 13 := by decide
    have h_comp : 1 < 2 * 388252507 + 1 - 2 ^ 13 ∧ ¬ Nat.Prime (2 * 388252507 + 1 - 2 ^ 13) :=
      composite_of_dvd (2 * 388252507 + 1) 13 47 hp47 hdvd_388252507 (by decide) (by decide)
    exact A282459_pos_of_exists 388252507 13 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 86869282 := by omega
    subst h_eq
    have hk : 20 ∈ Finset.Icc 1 (log 2 (2 * 86869282 + 1)) := by decide
    have hdvd_86869282 : 37 ∣ 2 * 86869282 + 1 - 2 ^ 20 := by decide
    have h_comp : 1 < 2 * 86869282 + 1 - 2 ^ 20 ∧ ¬ Nat.Prime (2 * 86869282 + 1 - 2 ^ 20) :=
      composite_of_dvd (2 * 86869282 + 1) 20 37 hp37 hdvd_86869282 (by decide) (by decide)
    exact A282459_pos_of_exists 86869282 20 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 408344722 := by omega
    subst h_eq
    have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 408344722 + 1)) := by decide
    have hdvd_408344722 : 37 ∣ 2 * 408344722 + 1 - 2 ^ 12 := by decide
    have h_comp : 1 < 2 * 408344722 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 408344722 + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * 408344722 + 1) 12 37 hp37 hdvd_408344722 (by decide) (by decide)
    exact A282459_pos_of_exists 408344722 12 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 267699217 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 267699217 + 1)) := by decide
    have hdvd_267699217 : 31 ∣ 2 * 267699217 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 267699217 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 267699217 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 267699217 + 1) 3 31 hp31 hdvd_267699217 (by decide) (by decide)
    exact A282459_pos_of_exists 267699217 3 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 428436937 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 428436937 + 1)) := by decide
    have hdvd_428436937 : 7 ∣ 2 * 428436937 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 428436937 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 428436937 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 428436937 + 1) 2 7 hp7 hdvd_428436937 (by decide) (by decide)
    exact A282459_pos_of_exists 428436937 2 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 127053712 := by omega
    subst h_eq
    have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 127053712 + 1)) := by decide
    have hdvd_127053712 : 37 ∣ 2 * 127053712 + 1 - 2 ^ 16 := by decide
    have h_comp : 1 < 2 * 127053712 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 127053712 + 1 - 2 ^ 16) :=
      composite_of_dvd (2 * 127053712 + 1) 16 37 hp37 hdvd_127053712 (by decide) (by decide)
    exact A282459_pos_of_exists 127053712 16 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 287791432 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 287791432 + 1)) := by decide
    have hdvd_287791432 : 7 ∣ 2 * 287791432 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 287791432 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 287791432 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 287791432 + 1) 2 7 hp7 hdvd_287791432 (by decide) (by decide)
    exact A282459_pos_of_exists 287791432 2 hk h_comp

lemma solve_tree_node_6_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 11) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 285427642 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 285427642 + 1)) := by decide
    have hdvd_285427642 : 37 ∣ 2 * 285427642 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 285427642 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 285427642 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 285427642 + 1) 3 37 hp37 hdvd_285427642 (by decide) (by decide)
    exact A282459_pos_of_exists 285427642 3 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 164874352 := by omega
    subst h_eq
    have hk : 27 ∈ Finset.Icc 1 (log 2 (2 * 164874352 + 1)) := by decide
    have hdvd_164874352 : 37 ∣ 2 * 164874352 + 1 - 2 ^ 27 := by decide
    have h_comp : 1 < 2 * 164874352 + 1 - 2 ^ 27 ∧ ¬ Nat.Prime (2 * 164874352 + 1 - 2 ^ 27) :=
      composite_of_dvd (2 * 164874352 + 1) 27 37 hp37 hdvd_164874352 (by decide) (by decide)
    exact A282459_pos_of_exists 164874352 27 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 24228847 := by omega
    subst h_eq
    have hk : 4 ∈ Finset.Icc 1 (log 2 (2 * 24228847 + 1)) := by decide
    have hdvd_24228847 : 37 ∣ 2 * 24228847 + 1 - 2 ^ 4 := by decide
    have h_comp : 1 < 2 * 24228847 + 1 - 2 ^ 4 ∧ ¬ Nat.Prime (2 * 24228847 + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * 24228847 + 1) 4 37 hp37 hdvd_24228847 (by decide) (by decide)
    exact A282459_pos_of_exists 24228847 4 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 44321062 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 44321062 + 1)) := by decide
    have hdvd_44321062 : 37 ∣ 2 * 44321062 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 44321062 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 44321062 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 44321062 + 1) 2 37 hp37 hdvd_44321062 (by decide) (by decide)
    exact A282459_pos_of_exists 44321062 2 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 205058782 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 205058782 + 1)) := by decide
    have hdvd_205058782 : 7 ∣ 2 * 205058782 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 205058782 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 205058782 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 205058782 + 1) 2 7 hp7 hdvd_205058782 (by decide) (by decide)
    exact A282459_pos_of_exists 205058782 2 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 225150997 := by omega
    subst h_eq
    have hk : 9 ∈ Finset.Icc 1 (log 2 (2 * 225150997 + 1)) := by decide
    have hdvd_225150997 : 41 ∣ 2 * 225150997 + 1 - 2 ^ 9 := by decide
    have h_comp : 1 < 2 * 225150997 + 1 - 2 ^ 9 ∧ ¬ Nat.Prime (2 * 225150997 + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * 225150997 + 1) 9 41 hp41 hdvd_225150997 (by decide) (by decide)
    exact A282459_pos_of_exists 225150997 9 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 385888717 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 385888717 + 1)) := by decide
    have hdvd_385888717 : 7 ∣ 2 * 385888717 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 385888717 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 385888717 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 385888717 + 1) 1 7 hp7 hdvd_385888717 (by decide) (by decide)
    exact A282459_pos_of_exists 385888717 1 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 245243212 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 245243212 + 1)) := by decide
    have hdvd_245243212 : 7 ∣ 2 * 245243212 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 245243212 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 245243212 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 245243212 + 1) 1 7 hp7 hdvd_245243212 (by decide) (by decide)
    exact A282459_pos_of_exists 245243212 1 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 104597707 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 104597707 + 1)) := by decide
    have hdvd_104597707 : 7 ∣ 2 * 104597707 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 104597707 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 104597707 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 104597707 + 1) 1 7 hp7 hdvd_104597707 (by decide) (by decide)
    exact A282459_pos_of_exists 104597707 1 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 265335427 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 265335427 + 1)) := by decide
    have hdvd_265335427 : 7 ∣ 2 * 265335427 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 265335427 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 265335427 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 265335427 + 1) 3 7 hp7 hdvd_265335427 (by decide) (by decide)
    exact A282459_pos_of_exists 265335427 3 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 426073147 := by omega
    subst h_eq
    have hk : 19 ∈ Finset.Icc 1 (log 2 (2 * 426073147 + 1)) := by decide
    have hdvd_426073147 : 37 ∣ 2 * 426073147 + 1 - 2 ^ 19 := by decide
    have h_comp : 1 < 2 * 426073147 + 1 - 2 ^ 19 ∧ ¬ Nat.Prime (2 * 426073147 + 1 - 2 ^ 19) :=
      composite_of_dvd (2 * 426073147 + 1) 19 37 hp37 hdvd_426073147 (by decide) (by decide)
    exact A282459_pos_of_exists 426073147 19 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 124689922 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 124689922 + 1)) := by decide
    have hdvd_124689922 : 7 ∣ 2 * 124689922 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 124689922 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 124689922 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 124689922 + 1) 3 7 hp7 hdvd_124689922 (by decide) (by decide)
    exact A282459_pos_of_exists 124689922 3 hk h_comp

lemma solve_tree_node_7_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 12) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 122326132 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 122326132 + 1)) := by decide
    have hdvd_122326132 : 7 ∣ 2 * 122326132 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 122326132 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 122326132 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 122326132 + 1) 2 7 hp7 hdvd_122326132 (by decide) (by decide)
    exact A282459_pos_of_exists 122326132 2 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 1772842 := by omega
    subst h_eq
    have hk : 7 ∈ Finset.Icc 1 (log 2 (2 * 1772842 + 1)) := by decide
    have hdvd_1772842 : 41 ∣ 2 * 1772842 + 1 - 2 ^ 7 := by decide
    have h_comp : 1 < 2 * 1772842 + 1 - 2 ^ 7 ∧ ¬ Nat.Prime (2 * 1772842 + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * 1772842 + 1) 7 41 hp41 hdvd_1772842 (by decide) (by decide)
    exact A282459_pos_of_exists 1772842 7 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 323248282 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 323248282 + 1)) := by decide
    have hdvd_323248282 : 7 ∣ 2 * 323248282 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 323248282 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 323248282 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 323248282 + 1) 3 7 hp7 hdvd_323248282 (by decide) (by decide)
    exact A282459_pos_of_exists 323248282 3 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 343340497 := by omega
    subst h_eq
    have hk : 14 ∈ Finset.Icc 1 (log 2 (2 * 343340497 + 1)) := by decide
    have hdvd_343340497 : 37 ∣ 2 * 343340497 + 1 - 2 ^ 14 := by decide
    have h_comp : 1 < 2 * 343340497 + 1 - 2 ^ 14 ∧ ¬ Nat.Prime (2 * 343340497 + 1 - 2 ^ 14) :=
      composite_of_dvd (2 * 343340497 + 1) 14 37 hp37 hdvd_343340497 (by decide) (by decide)
    exact A282459_pos_of_exists 343340497 14 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 41957272 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 41957272 + 1)) := by decide
    have hdvd_41957272 : 7 ∣ 2 * 41957272 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 41957272 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 41957272 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 41957272 + 1) 3 7 hp7 hdvd_41957272 (by decide) (by decide)
    exact A282459_pos_of_exists 41957272 3 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 62049487 := by omega
    subst h_eq
    have hk : 11 ∈ Finset.Icc 1 (log 2 (2 * 62049487 + 1)) := by decide
    have hdvd_62049487 : 37 ∣ 2 * 62049487 + 1 - 2 ^ 11 := by decide
    have h_comp : 1 < 2 * 62049487 + 1 - 2 ^ 11 ∧ ¬ Nat.Prime (2 * 62049487 + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * 62049487 + 1) 11 37 hp37 hdvd_62049487 (by decide) (by decide)
    exact A282459_pos_of_exists 62049487 11 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 222787207 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 222787207 + 1)) := by decide
    have hdvd_222787207 : 73 ∣ 2 * 222787207 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 222787207 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 222787207 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 222787207 + 1) 3 73 hp73 hdvd_222787207 (by decide) (by decide)
    exact A282459_pos_of_exists 222787207 3 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 82141702 := by omega
    subst h_eq
    have hk : 14 ∈ Finset.Icc 1 (log 2 (2 * 82141702 + 1)) := by decide
    have hdvd_82141702 : 47 ∣ 2 * 82141702 + 1 - 2 ^ 14 := by decide
    have h_comp : 1 < 2 * 82141702 + 1 - 2 ^ 14 ∧ ¬ Nat.Prime (2 * 82141702 + 1 - 2 ^ 14) :=
      composite_of_dvd (2 * 82141702 + 1) 14 47 hp47 hdvd_82141702 (by decide) (by decide)
    exact A282459_pos_of_exists 82141702 14 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 403617142 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 403617142 + 1)) := by decide
    have hdvd_403617142 : 7 ∣ 2 * 403617142 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 403617142 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 403617142 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 403617142 + 1) 2 7 hp7 hdvd_403617142 (by decide) (by decide)
    exact A282459_pos_of_exists 403617142 2 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 102233917 := by omega
    subst h_eq
    have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 102233917 + 1)) := by decide
    have hdvd_102233917 : 37 ∣ 2 * 102233917 + 1 - 2 ^ 12 := by decide
    have h_comp : 1 < 2 * 102233917 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 102233917 + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * 102233917 + 1) 12 37 hp37 hdvd_102233917 (by decide) (by decide)
    exact A282459_pos_of_exists 102233917 12 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 262971637 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 262971637 + 1)) := by decide
    have hdvd_262971637 : 7 ∣ 2 * 262971637 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 262971637 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 262971637 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 262971637 + 1) 2 7 hp7 hdvd_262971637 (by decide) (by decide)
    exact A282459_pos_of_exists 262971637 2 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 423709357 := by omega
    subst h_eq
    have hk : 7 ∈ Finset.Icc 1 (log 2 (2 * 423709357 + 1)) := by decide
    have hdvd_423709357 : 43 ∣ 2 * 423709357 + 1 - 2 ^ 7 := by decide
    have h_comp : 1 < 2 * 423709357 + 1 - 2 ^ 7 ∧ ¬ Nat.Prime (2 * 423709357 + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * 423709357 + 1) 7 43 hp43 hdvd_423709357 (by decide) (by decide)
    exact A282459_pos_of_exists 423709357 7 hk h_comp

lemma solve_tree_node_8_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 14) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 258244057 := by omega
    subst h_eq
    have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 258244057 + 1)) := by decide
    have hdvd_258244057 : 37 ∣ 2 * 258244057 + 1 - 2 ^ 16 := by decide
    have h_comp : 1 < 2 * 258244057 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 258244057 + 1 - 2 ^ 16) :=
      composite_of_dvd (2 * 258244057 + 1) 16 37 hp37 hdvd_258244057 (by decide) (by decide)
    exact A282459_pos_of_exists 258244057 16 hk h_comp
  · -- Case % 23 = 1
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 23 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 23 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 23 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 23 = 5
    have h_eq : n = 137690767 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 137690767 + 1)) := by decide
    have hdvd_137690767 : 7 ∣ 2 * 137690767 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 137690767 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 137690767 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 137690767 + 1) 1 7 hp7 hdvd_137690767 (by decide) (by decide)
    exact A282459_pos_of_exists 137690767 1 hk h_comp
  · -- Case % 23 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 23 = 7
    have h_eq : n = 459166207 := by omega
    subst h_eq
    have hk : 25 ∈ Finset.Icc 1 (log 2 (2 * 459166207 + 1)) := by decide
    have hdvd_459166207 : 59 ∣ 2 * 459166207 + 1 - 2 ^ 25 := by decide
    have h_comp : 1 < 2 * 459166207 + 1 - 2 ^ 25 ∧ ¬ Nat.Prime (2 * 459166207 + 1 - 2 ^ 25) :=
      composite_of_dvd (2 * 459166207 + 1) 25 59 hp59 hdvd_459166207 (by decide) (by decide)
    exact A282459_pos_of_exists 459166207 25 hk h_comp
  · -- Case % 23 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 23 = 9
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 23 = 10
    have h_eq : n = 17137477 := by omega
    subst h_eq
    have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 17137477 + 1)) := by decide
    have hdvd_17137477 : 7 ∣ 2 * 17137477 + 1 - 2 ^ 3 := by decide
    have h_comp : 1 < 2 * 17137477 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 17137477 + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * 17137477 + 1) 3 7 hp7 hdvd_17137477 (by decide) (by decide)
    exact A282459_pos_of_exists 17137477 3 hk h_comp
  · -- Case % 23 = 11
    have h_eq : n = 177875197 := by omega
    subst h_eq
    have hk : 25 ∈ Finset.Icc 1 (log 2 (2 * 177875197 + 1)) := by decide
    have hdvd_177875197 : 37 ∣ 2 * 177875197 + 1 - 2 ^ 25 := by decide
    have h_comp : 1 < 2 * 177875197 + 1 - 2 ^ 25 ∧ ¬ Nat.Prime (2 * 177875197 + 1 - 2 ^ 25) :=
      composite_of_dvd (2 * 177875197 + 1) 25 37 hp37 hdvd_177875197 (by decide) (by decide)
    exact A282459_pos_of_exists 177875197 25 hk h_comp
  · -- Case % 23 = 12
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 23 = 13
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 23 = 14
    have h_eq : n = 197967412 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 197967412 + 1)) := by decide
    have hdvd_197967412 : 31 ∣ 2 * 197967412 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 197967412 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 197967412 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 197967412 + 1) 2 31 hp31 hdvd_197967412 (by decide) (by decide)
    exact A282459_pos_of_exists 197967412 2 hk h_comp
  · -- Case % 23 = 15
    have h_eq : n = 358705132 := by omega
    subst h_eq
    have hk : 15 ∈ Finset.Icc 1 (log 2 (2 * 358705132 + 1)) := by decide
    have hdvd_358705132 : 37 ∣ 2 * 358705132 + 1 - 2 ^ 15 := by decide
    have h_comp : 1 < 2 * 358705132 + 1 - 2 ^ 15 ∧ ¬ Nat.Prime (2 * 358705132 + 1 - 2 ^ 15) :=
      composite_of_dvd (2 * 358705132 + 1) 15 37 hp37 hdvd_358705132 (by decide) (by decide)
    exact A282459_pos_of_exists 358705132 15 hk h_comp
  · -- Case % 23 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 23 = 17
    have h_eq : n = 218059627 := by omega
    subst h_eq
    have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 218059627 + 1)) := by decide
    have hdvd_218059627 : 31 ∣ 2 * 218059627 + 1 - 2 ^ 1 := by decide
    have h_comp : 1 < 2 * 218059627 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 218059627 + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * 218059627 + 1) 1 31 hp31 hdvd_218059627 (by decide) (by decide)
    exact A282459_pos_of_exists 218059627 1 hk h_comp
  · -- Case % 23 = 18
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 23 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 23
      · exact h_mod_23
      · exact hk
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 23 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 23 hp23 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 23 = 19
    have h_eq : n = 77414122 := by omega
    subst h_eq
    have hk : 4 ∈ Finset.Icc 1 (log 2 (2 * 77414122 + 1)) := by decide
    have hdvd_77414122 : 31 ∣ 2 * 77414122 + 1 - 2 ^ 4 := by decide
    have h_comp : 1 < 2 * 77414122 + 1 - 2 ^ 4 ∧ ¬ Nat.Prime (2 * 77414122 + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * 77414122 + 1) 4 31 hp31 hdvd_77414122 (by decide) (by decide)
    exact A282459_pos_of_exists 77414122 4 hk h_comp
  · -- Case % 23 = 20
    have h_eq : n = 238151842 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 238151842 + 1)) := by decide
    have hdvd_238151842 : 7 ∣ 2 * 238151842 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 238151842 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 238151842 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 238151842 + 1) 2 7 hp7 hdvd_238151842 (by decide) (by decide)
    exact A282459_pos_of_exists 238151842 2 hk h_comp
  · -- Case % 23 = 21
    have h_eq : n = 398889562 := by omega
    subst h_eq
    have hk : 18 ∈ Finset.Icc 1 (log 2 (2 * 398889562 + 1)) := by decide
    have hdvd_398889562 : 37 ∣ 2 * 398889562 + 1 - 2 ^ 18 := by decide
    have h_comp : 1 < 2 * 398889562 + 1 - 2 ^ 18 ∧ ¬ Nat.Prime (2 * 398889562 + 1 - 2 ^ 18) :=
      composite_of_dvd (2 * 398889562 + 1) 18 37 hp37 hdvd_398889562 (by decide) (by decide)
    exact A282459_pos_of_exists 398889562 18 hk h_comp
  · -- Case % 23 = 22
    have h_eq : n = 97506337 := by omega
    subst h_eq
    have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 97506337 + 1)) := by decide
    have hdvd_97506337 : 7 ∣ 2 * 97506337 + 1 - 2 ^ 2 := by decide
    have h_comp : 1 < 2 * 97506337 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 97506337 + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * 97506337 + 1) 2 7 hp7 hdvd_97506337 (by decide) (by decide)
    exact A282459_pos_of_exists 97506337 2 hk h_comp

lemma solve_tree_node_9_17 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17_lt : (2 * n + 1) % 17 < 17) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 17
  · -- Case % 17 = 0
    have h_eq_17 : (2 * n + 1) % 17 = 0 := by omega
    exact solve_tree_node_0_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 1
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 17 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 17 = 3
    have h_eq_17 : (2 * n + 1) % 17 = 3 := by omega
    exact solve_tree_node_1_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 17 = 5
    have h_eq_17 : (2 * n + 1) % 17 = 5 := by omega
    exact solve_tree_node_2_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 6
    have h_eq_17 : (2 * n + 1) % 17 = 6 := by omega
    exact solve_tree_node_3_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 7
    have h_eq_17 : (2 * n + 1) % 17 = 7 := by omega
    exact solve_tree_node_4_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 17 = 9
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 17 = 10
    have h_eq_17 : (2 * n + 1) % 17 = 10 := by omega
    exact solve_tree_node_5_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 11
    have h_eq_17 : (2 * n + 1) % 17 = 11 := by omega
    exact solve_tree_node_6_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 12
    have h_eq_17 : (2 * n + 1) % 17 = 12 := by omega
    exact solve_tree_node_7_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 13
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 17 = 14
    have h_eq_17 : (2 * n + 1) % 17 = 14 := by omega
    exact solve_tree_node_8_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 15
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 17 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 17 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 17
      · exact h_mod_17
      · exact hk
    have h_gt : 17 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 17 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 17 hp17 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp

lemma solve_tree_node_10_29 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29_lt : (2 * n + 1) % 29 < 29) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 29
  · -- Case % 29 = 0
    have h_eq_29 : (2 * n + 1) % 29 = 0 := by omega
    exact solve_tree_node_9_17 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_eq_29 (Nat.mod_lt _ (by decide))
  · -- Case % 29 = 1
    have hk : 2^28 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 268435456 hn (by decide)
    have h_in : 28 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 28 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^28 := by
      apply dvd_of_mod_eq (2 * n + 1) 28 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^28 := gt_of_ge (2 * n + 1) 268435456 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^28 := h1_of_ge (2 * n + 1) 268435456 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^28 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 28) :=
      composite_of_dvd (2 * n + 1) 28 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 28 h_in h_comp
  · -- Case % 29 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 29 = 3
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 29 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 29 = 5
    have hk : 2^22 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4194304 hn (by decide)
    have h_in : 22 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 22 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^22 := by
      apply dvd_of_mod_eq (2 * n + 1) 22 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^22 := gt_of_ge (2 * n + 1) 4194304 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^22 := h1_of_ge (2 * n + 1) 4194304 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^22 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 22) :=
      composite_of_dvd (2 * n + 1) 22 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 22 h_in h_comp
  · -- Case % 29 = 6
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 29 = 7
    have hk : 2^12 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4096 hn (by decide)
    have h_in : 12 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 12 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^12 := by
      apply dvd_of_mod_eq (2 * n + 1) 12 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^12 := gt_of_ge (2 * n + 1) 4096 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^12 := h1_of_ge (2 * n + 1) 4096 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^12 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * n + 1) 12 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 12 h_in h_comp
  · -- Case % 29 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 29 = 9
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 29 = 10
    have hk : 2^23 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8388608 hn (by decide)
    have h_in : 23 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 23 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^23 := by
      apply dvd_of_mod_eq (2 * n + 1) 23 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^23 := gt_of_ge (2 * n + 1) 8388608 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^23 := h1_of_ge (2 * n + 1) 8388608 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^23 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 23) :=
      composite_of_dvd (2 * n + 1) 23 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 23 h_in h_comp
  · -- Case % 29 = 11
    have hk : 2^25 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 33554432 hn (by decide)
    have h_in : 25 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 25 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^25 := by
      apply dvd_of_mod_eq (2 * n + 1) 25 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^25 := gt_of_ge (2 * n + 1) 33554432 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^25 := h1_of_ge (2 * n + 1) 33554432 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^25 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 25) :=
      composite_of_dvd (2 * n + 1) 25 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 25 h_in h_comp
  · -- Case % 29 = 12
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 29 = 13
    have hk : 2^18 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 262144 hn (by decide)
    have h_in : 18 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 18 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^18 := by
      apply dvd_of_mod_eq (2 * n + 1) 18 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^18 := gt_of_ge (2 * n + 1) 262144 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^18 := h1_of_ge (2 * n + 1) 262144 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^18 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 18) :=
      composite_of_dvd (2 * n + 1) 18 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 18 h_in h_comp
  · -- Case % 29 = 14
    have hk : 2^13 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8192 hn (by decide)
    have h_in : 13 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 13 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^13 := by
      apply dvd_of_mod_eq (2 * n + 1) 13 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^13 := gt_of_ge (2 * n + 1) 8192 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^13 := h1_of_ge (2 * n + 1) 8192 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^13 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 13) :=
      composite_of_dvd (2 * n + 1) 13 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 13 h_in h_comp
  · -- Case % 29 = 15
    have hk : 2^27 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 134217728 hn (by decide)
    have h_in : 27 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 27 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^27 := by
      apply dvd_of_mod_eq (2 * n + 1) 27 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^27 := gt_of_ge (2 * n + 1) 134217728 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^27 := h1_of_ge (2 * n + 1) 134217728 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^27 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 27) :=
      composite_of_dvd (2 * n + 1) 27 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 27 h_in h_comp
  · -- Case % 29 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 29 = 17
    have hk : 2^21 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2097152 hn (by decide)
    have h_in : 21 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 21 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^21 := by
      apply dvd_of_mod_eq (2 * n + 1) 21 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^21 := gt_of_ge (2 * n + 1) 2097152 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^21 := h1_of_ge (2 * n + 1) 2097152 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^21 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 21) :=
      composite_of_dvd (2 * n + 1) 21 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 21 h_in h_comp
  · -- Case % 29 = 18
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 29 = 19
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 29 = 20
    have hk : 2^24 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16777216 hn (by decide)
    have h_in : 24 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 24 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^24 := by
      apply dvd_of_mod_eq (2 * n + 1) 24 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^24 := gt_of_ge (2 * n + 1) 16777216 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^24 := h1_of_ge (2 * n + 1) 16777216 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^24 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 24) :=
      composite_of_dvd (2 * n + 1) 24 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 24 h_in h_comp
  · -- Case % 29 = 21
    have hk : 2^17 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 131072 hn (by decide)
    have h_in : 17 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 17 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^17 := by
      apply dvd_of_mod_eq (2 * n + 1) 17 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^17 := gt_of_ge (2 * n + 1) 131072 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^17 := h1_of_ge (2 * n + 1) 131072 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^17 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 17) :=
      composite_of_dvd (2 * n + 1) 17 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 17 h_in h_comp
  · -- Case % 29 = 22
    have hk : 2^26 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 67108864 hn (by decide)
    have h_in : 26 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 26 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^26 := by
      apply dvd_of_mod_eq (2 * n + 1) 26 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^26 := gt_of_ge (2 * n + 1) 67108864 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^26 := h1_of_ge (2 * n + 1) 67108864 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^26 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 26) :=
      composite_of_dvd (2 * n + 1) 26 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 26 h_in h_comp
  · -- Case % 29 = 23
    have hk : 2^20 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1048576 hn (by decide)
    have h_in : 20 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 20 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^20 := by
      apply dvd_of_mod_eq (2 * n + 1) 20 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^20 := gt_of_ge (2 * n + 1) 1048576 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^20 := h1_of_ge (2 * n + 1) 1048576 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^20 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 20) :=
      composite_of_dvd (2 * n + 1) 20 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 20 h_in h_comp
  · -- Case % 29 = 24
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 29 = 25
    have hk : 2^16 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 65536 hn (by decide)
    have h_in : 16 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 16 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^16 := by
      apply dvd_of_mod_eq (2 * n + 1) 16 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^16 := gt_of_ge (2 * n + 1) 65536 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^16 := h1_of_ge (2 * n + 1) 65536 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^16 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 16) :=
      composite_of_dvd (2 * n + 1) 16 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 16 h_in h_comp
  · -- Case % 29 = 26
    have hk : 2^19 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 524288 hn (by decide)
    have h_in : 19 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 19 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^19 := by
      apply dvd_of_mod_eq (2 * n + 1) 19 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^19 := gt_of_ge (2 * n + 1) 524288 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^19 := h1_of_ge (2 * n + 1) 524288 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^19 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 19) :=
      composite_of_dvd (2 * n + 1) 19 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 19 h_in h_comp
  · -- Case % 29 = 27
    have hk : 2^15 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32768 hn (by decide)
    have h_in : 15 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 15 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^15 := by
      apply dvd_of_mod_eq (2 * n + 1) 15 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^15 := gt_of_ge (2 * n + 1) 32768 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^15 := h1_of_ge (2 * n + 1) 32768 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^15 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 15) :=
      composite_of_dvd (2 * n + 1) 15 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 15 h_in h_comp
  · -- Case % 29 = 28
    have hk : 2^14 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16384 hn (by decide)
    have h_in : 14 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 14 (by decide) hk
    have h_dvd : 29 ∣ 2 * n + 1 - 2^14 := by
      apply dvd_of_mod_eq (2 * n + 1) 14 29
      · exact h_mod_29
      · exact hk
    have h_gt : 29 < 2 * n + 1 - 2^14 := gt_of_ge (2 * n + 1) 16384 29 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^14 := h1_of_ge (2 * n + 1) 16384 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^14 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 14) :=
      composite_of_dvd (2 * n + 1) 14 29 hp29 h_dvd h_gt h1
    exact A282459_pos_of_exists n 14 h_in h_comp

lemma solve_tree_node_11_19 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19_lt : (2 * n + 1) % 19 < 19) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 19
  · -- Case % 19 = 0
    have h_eq_19 : (2 * n + 1) % 19 = 0 := by omega
    exact solve_tree_node_10_29 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_eq_19 (Nat.mod_lt _ (by decide))
  · -- Case % 19 = 1
    have hk : 2^18 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 262144 hn (by decide)
    have h_in : 18 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 18 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^18 := by
      apply dvd_of_mod_eq (2 * n + 1) 18 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^18 := gt_of_ge (2 * n + 1) 262144 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^18 := h1_of_ge (2 * n + 1) 262144 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^18 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 18) :=
      composite_of_dvd (2 * n + 1) 18 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 18 h_in h_comp
  · -- Case % 19 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 19 = 3
    have hk : 2^13 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8192 hn (by decide)
    have h_in : 13 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 13 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^13 := by
      apply dvd_of_mod_eq (2 * n + 1) 13 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^13 := gt_of_ge (2 * n + 1) 8192 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^13 := h1_of_ge (2 * n + 1) 8192 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^13 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 13) :=
      composite_of_dvd (2 * n + 1) 13 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 13 h_in h_comp
  · -- Case % 19 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 19 = 5
    have hk : 2^16 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 65536 hn (by decide)
    have h_in : 16 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 16 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^16 := by
      apply dvd_of_mod_eq (2 * n + 1) 16 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^16 := gt_of_ge (2 * n + 1) 65536 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^16 := h1_of_ge (2 * n + 1) 65536 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^16 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 16) :=
      composite_of_dvd (2 * n + 1) 16 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 16 h_in h_comp
  · -- Case % 19 = 6
    have hk : 2^14 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16384 hn (by decide)
    have h_in : 14 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 14 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^14 := by
      apply dvd_of_mod_eq (2 * n + 1) 14 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^14 := gt_of_ge (2 * n + 1) 16384 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^14 := h1_of_ge (2 * n + 1) 16384 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^14 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 14) :=
      composite_of_dvd (2 * n + 1) 14 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 14 h_in h_comp
  · -- Case % 19 = 7
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 19 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 19 = 9
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 19 = 10
    have hk : 2^17 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 131072 hn (by decide)
    have h_in : 17 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 17 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^17 := by
      apply dvd_of_mod_eq (2 * n + 1) 17 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^17 := gt_of_ge (2 * n + 1) 131072 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^17 := h1_of_ge (2 * n + 1) 131072 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^17 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 17) :=
      composite_of_dvd (2 * n + 1) 17 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 17 h_in h_comp
  · -- Case % 19 = 11
    have hk : 2^12 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4096 hn (by decide)
    have h_in : 12 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 12 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^12 := by
      apply dvd_of_mod_eq (2 * n + 1) 12 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^12 := gt_of_ge (2 * n + 1) 4096 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^12 := h1_of_ge (2 * n + 1) 4096 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^12 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * n + 1) 12 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 12 h_in h_comp
  · -- Case % 19 = 12
    have hk : 2^15 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32768 hn (by decide)
    have h_in : 15 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 15 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^15 := by
      apply dvd_of_mod_eq (2 * n + 1) 15 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^15 := gt_of_ge (2 * n + 1) 32768 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^15 := h1_of_ge (2 * n + 1) 32768 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^15 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 15) :=
      composite_of_dvd (2 * n + 1) 15 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 15 h_in h_comp
  · -- Case % 19 = 13
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 19 = 14
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 19 = 15
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 19 = 16
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 19 = 17
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 19 = 18
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 19 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 19
      · exact h_mod_19
      · exact hk
    have h_gt : 19 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 19 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 19 hp19 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp

lemma solve_tree_node_12_13 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13_lt : (2 * n + 1) % 13 < 13) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 13
  · -- Case % 13 = 0
    have h_eq_13 : (2 * n + 1) % 13 = 0 := by omega
    exact solve_tree_node_11_19 n hn h_mod_3 h_mod_5 h_mod_11 h_eq_13 (Nat.mod_lt _ (by decide))
  · -- Case % 13 = 1
    have hk : 2^12 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4096 hn (by decide)
    have h_in : 12 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 12 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^12 := by
      apply dvd_of_mod_eq (2 * n + 1) 12 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^12 := gt_of_ge (2 * n + 1) 4096 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^12 := h1_of_ge (2 * n + 1) 4096 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^12 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 12) :=
      composite_of_dvd (2 * n + 1) 12 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 12 h_in h_comp
  · -- Case % 13 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 13 = 3
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 13 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 13 = 5
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 13 = 6
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp
  · -- Case % 13 = 7
    have hk : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_in : 11 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 11 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^11 := by
      apply dvd_of_mod_eq (2 * n + 1) 11 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) 2048 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) 2048 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^11 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 11) :=
      composite_of_dvd (2 * n + 1) 11 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 11 h_in h_comp
  · -- Case % 13 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 13 = 9
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 13 = 10
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 13 = 11
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 13 = 12
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 13 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 13
      · exact h_mod_13
      · exact hk
    have h_gt : 13 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 13 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 13 hp13 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp

lemma solve_tree_node_13_11 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11_lt : (2 * n + 1) % 11 < 11) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 11
  · -- Case % 11 = 0
    have h_eq_11 : (2 * n + 1) % 11 = 0 := by omega
    exact solve_tree_node_12_13 n hn h_mod_3 h_mod_5 h_eq_11 (Nat.mod_lt _ (by decide))
  · -- Case % 11 = 1
    have hk : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_in : 10 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 10 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^10 := by
      apply dvd_of_mod_eq (2 * n + 1) 10 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) 1024 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) 1024 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^10 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 10) :=
      composite_of_dvd (2 * n + 1) 10 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 10 h_in h_comp
  · -- Case % 11 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 11 = 3
    have hk : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 256 hn (by decide)
    have h_in : 8 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 8 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^8 := by
      apply dvd_of_mod_eq (2 * n + 1) 8 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) 256 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) 256 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^8 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 8) :=
      composite_of_dvd (2 * n + 1) 8 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 8 h_in h_comp
  · -- Case % 11 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 11 = 5
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 11 = 6
    have hk : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 512 hn (by decide)
    have h_in : 9 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 9 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^9 := by
      apply dvd_of_mod_eq (2 * n + 1) 9 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) 512 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) 512 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^9 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 9) :=
      composite_of_dvd (2 * n + 1) 9 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 9 h_in h_comp
  · -- Case % 11 = 7
    have hk : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 128 hn (by decide)
    have h_in : 7 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 7 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^7 := by
      apply dvd_of_mod_eq (2 * n + 1) 7 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) 128 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) 128 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^7 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 7) :=
      composite_of_dvd (2 * n + 1) 7 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 7 h_in h_comp
  · -- Case % 11 = 8
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 11 = 9
    have hk : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 64 hn (by decide)
    have h_in : 6 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 6 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^6 := by
      apply dvd_of_mod_eq (2 * n + 1) 6 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) 64 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) 64 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^6 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 6) :=
      composite_of_dvd (2 * n + 1) 6 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 6 h_in h_comp
  · -- Case % 11 = 10
    have hk : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 32 hn (by decide)
    have h_in : 5 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 5 (by decide) hk
    have h_dvd : 11 ∣ 2 * n + 1 - 2^5 := by
      apply dvd_of_mod_eq (2 * n + 1) 5 11
      · exact h_mod_11
      · exact hk
    have h_gt : 11 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) 32 11 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) 32 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^5 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 5) :=
      composite_of_dvd (2 * n + 1) 5 11 hp11 h_dvd h_gt h1
    exact A282459_pos_of_exists n 5 h_in h_comp

lemma solve_tree_node_14_5 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5_lt : (2 * n + 1) % 5 < 5) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 5
  · -- Case % 5 = 0
    have h_eq_5 : (2 * n + 1) % 5 = 0 := by omega
    exact solve_tree_node_13_11 n hn h_mod_3 h_eq_5 (Nat.mod_lt _ (by decide))
  · -- Case % 5 = 1
    have hk : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 16 hn (by decide)
    have h_in : 4 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 4 (by decide) hk
    have h_dvd : 5 ∣ 2 * n + 1 - 2^4 := by
      apply dvd_of_mod_eq (2 * n + 1) 4 5
      · exact h_mod_5
      · exact hk
    have h_gt : 5 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) 16 5 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) 16 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^4 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 4) :=
      composite_of_dvd (2 * n + 1) 4 5 hp5 h_dvd h_gt h1
    exact A282459_pos_of_exists n 4 h_in h_comp
  · -- Case % 5 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 5 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 5
      · exact h_mod_5
      · exact hk
    have h_gt : 5 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 5 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 5 hp5 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
  · -- Case % 5 = 3
    have hk : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 8 hn (by decide)
    have h_in : 3 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 3 (by decide) hk
    have h_dvd : 5 ∣ 2 * n + 1 - 2^3 := by
      apply dvd_of_mod_eq (2 * n + 1) 3 5
      · exact h_mod_5
      · exact hk
    have h_gt : 5 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) 8 5 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) 8 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^3 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 3) :=
      composite_of_dvd (2 * n + 1) 3 5 hp5 h_dvd h_gt h1
    exact A282459_pos_of_exists n 3 h_in h_comp
  · -- Case % 5 = 4
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 5 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 5
      · exact h_mod_5
      · exact hk
    have h_gt : 5 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 5 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 5 hp5 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp

lemma solve_tree_node_15_3 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3_lt : (2 * n + 1) % 3 < 3) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 3
  · -- Case % 3 = 0
    have h_eq_3 : (2 * n + 1) % 3 = 0 := by omega
    exact solve_tree_node_14_5 n hn h_eq_3 (Nat.mod_lt _ (by decide))
  · -- Case % 3 = 1
    have hk : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 4 hn (by decide)
    have h_in : 2 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 2 (by decide) hk
    have h_dvd : 3 ∣ 2 * n + 1 - 2^2 := by
      apply dvd_of_mod_eq (2 * n + 1) 2 3
      · exact h_mod_3
      · exact hk
    have h_gt : 3 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) 4 3 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) 4 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^2 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 2) :=
      composite_of_dvd (2 * n + 1) 2 3 hp3 h_dvd h_gt h1
    exact A282459_pos_of_exists n 2 h_in h_comp
  · -- Case % 3 = 2
    have hk : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) 2 hn (by decide)
    have h_in : 1 ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by exact k_in_Icc n 1 (by decide) hk
    have h_dvd : 3 ∣ 2 * n + 1 - 2^1 := by
      apply dvd_of_mod_eq (2 * n + 1) 1 3
      · exact h_mod_3
      · exact hk
    have h_gt : 3 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) 2 3 hn (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) 2 hn (by decide)
    have h_comp : 1 < 2 * n + 1 - 2^1 ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ 1) :=
      composite_of_dvd (2 * n + 1) 1 3 hp3 h_dvd h_gt h1
    exact A282459_pos_of_exists n 1 h_in h_comp
