import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/--
A289827: $a(n)$ is the largest $m \le n$ such that $\pi(m + n) = \pi(m) + \pi(n)$, where $\pi$ is the prime counting function $\text{A000720}$ ($\pi(0) = 0$).
-/
noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n

lemma findGreatest_le_ten (n : ℕ) (hn : 10 ≤ n)
    (h_neq : ∀ m, 11 ≤ m → m ≤ n → Nat.primeCounting (m + n) ≠ Nat.primeCounting m + Nat.primeCounting n) :
    A289827 n ≤ 10 := by
  have h_le : A289827 n ≤ n := Nat.findGreatest_le _
  by_cases h_zero : A289827 n = 0
  · omega
  · have h_spec := Nat.findGreatest_of_ne_zero rfl h_zero
    by_contra h_gt
    have h_gt : 11 ≤ A289827 n := by omega
    have h_neq_spec := h_neq (A289827 n) h_gt h_le
    exact h_neq_spec h_spec

lemma primeCounting_add_eleven (n : ℕ) (hn : 10 ≤ n) :
    Nat.primeCounting (11 + n) < Nat.primeCounting 11 + Nat.primeCounting n := by
  have h_add := Nat.primeCounting'_add_le (a := 6) (k := n + 1) (by decide) (by omega) 11
  have h_totient : Nat.totient 6 = 2 := by decide
  have h_div : 11 / 6 + 1 = 2 := by decide
  have h_pi_eleven : Nat.primeCounting 11 = 5 := by decide
  have h_eq1 : Nat.primeCounting (11 + n) = Nat.primeCounting' (n + 1 + 11) := by
    rw [Nat.primeCounting]
    congr 1
    omega
  have h_eq2 : Nat.primeCounting n = Nat.primeCounting' (n + 1) := rfl
  rw [h_eq1, h_eq2] at *
  rw [h_totient, h_div] at h_add
  omega

lemma primeCounting_succ_eq_succ (n : ℕ) : Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 ↔ (n + 1).Prime := by
  -- Nat.primeCounting is defined using Nat.primeCounting' and count
  rw [Nat.primeCounting, Nat.primeCounting]
  -- primeCounting' (n + 1 + 1) is primeCounting' (n + 2)
  have h1 : n + 1 + 1 = n + 2 := by omega
  have h2 : n + 1 = n + 1 := rfl
  rw [h1, h2]
  -- primeCounting' is count Prime
  exact Nat.count_succ_eq_succ_count_iff

lemma primeCounting_succ_eq_self (n : ℕ) : Nat.primeCounting (n + 1) = Nat.primeCounting n ↔ ¬ (n + 1).Prime := by
  rw [Nat.primeCounting, Nat.primeCounting]
  have h1 : n + 1 + 1 = n + 2 := by omega
  have h2 : n + 1 = n + 1 := rfl
  rw [h1, h2]
  exact Nat.count_succ_eq_count_iff

lemma prime_consecutive_contradiction (n : ℕ) (hn : 2 < n) (hp1 : (n + 1).Prime) (hp2 : (n + 2).Prime) : False := by
  have h_even_or_odd := Nat.even_or_odd (n + 1)
  rcases h_even_or_odd with h_even | h_odd
  · -- n + 1 is even. Since n + 1 is prime, n + 1 = 2
    have h_eq : n + 1 = 2 := hp1.even_iff.mp h_even
    omega
  · -- n + 1 is odd. Then n + 2 is even
    have h_even2 : (n + 2) % 2 = 0 := by
      -- n + 1 is odd means (n + 1) % 2 = 1
      have : (n + 1) % 2 = 1 := Nat.odd_iff.mp h_odd
      omega
    have h_even2' : Even (n + 2) := Nat.even_iff.mpr h_even2
    have h_eq2 : n + 2 = 2 := hp2.even_iff.mp h_even2'
    omega

lemma prime_three_consecutive_odds_contradiction (n : ℕ) (hn : 2 < n) (hp1 : (n + 1).Prime) (hp3 : (n + 3).Prime) (hp5 : (n + 5).Prime) : False := by
  have h_mod : (n + 1) % 3 = 0 ∨ (n + 3) % 3 = 0 ∨ (n + 5) % 3 = 0 := by omega
  rcases h_mod with h1 | h3 | h5
  · have h_dvd : 3 ∣ n + 1 := Nat.dvd_of_mod_eq_zero h1
    have h_eq : n + 1 = 3 := ((Nat.Prime.eq_one_or_self_of_dvd hp1 3 h_dvd).resolve_left (by decide)).symm
    omega
  · have h_dvd : 3 ∣ n + 3 := Nat.dvd_of_mod_eq_zero h3
    have h_eq : n + 3 = 3 := ((Nat.Prime.eq_one_or_self_of_dvd hp3 3 h_dvd).resolve_left (by decide)).symm
    omega
  · have h_dvd : 3 ∣ n + 5 := Nat.dvd_of_mod_eq_zero h5
    have h_eq : n + 5 = 3 := ((Nat.Prime.eq_one_or_self_of_dvd hp5 3 h_dvd).resolve_left (by decide)).symm
    omega

lemma not_prime_of_mod_two_eq_zero (x : ℕ) (h_mod : x % 2 = 0) (h_gt : 2 < x) : ¬ x.Prime := by
  intro hp
  have h_even : Even x := Nat.even_iff.mpr h_mod
  have h_eq : x = 2 := hp.even_iff.mp h_even
  omega



lemma primeCounting_le_succ (a : ℕ) : Nat.primeCounting a ≤ Nat.primeCounting (a + 1) := by
  by_cases hp : (a + 1).Prime
  · rw [(primeCounting_succ_eq_succ a).mpr hp]
    omega
  · rw [(primeCounting_succ_eq_self a).mpr hp]

lemma primeCounting_succ_le (a : ℕ) : Nat.primeCounting (a + 1) ≤ Nat.primeCounting a + 1 := by
  by_cases hp : (a + 1).Prime
  · rw [(primeCounting_succ_eq_succ a).mpr hp]
  · rw [(primeCounting_succ_eq_self a).mpr hp]
    omega


lemma primeCounting_add_two_le (n : ℕ) (hn : 2 < n) : Nat.primeCounting (n + 2) ≤ Nat.primeCounting n + 1 := by
  by_cases hp1 : (n + 1).Prime
  · have h_pc1 : Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 := (primeCounting_succ_eq_succ n).mpr hp1
    have hp2 : ¬ (n + 2).Prime := prime_consecutive_contradiction n hn hp1
    have h_pc2 : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
      have : n + 2 = n + 1 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 1)).mpr (by rwa [this] at hp2)
    omega
  · have h_pc1 : Nat.primeCounting (n + 1) = Nat.primeCounting n := (primeCounting_succ_eq_self n).mpr hp1
    by_cases hp2 : (n + 2).Prime
    · have h_pc2 : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) + 1 := by
        have : n + 2 = n + 1 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_succ (n + 1)).mpr (by rwa [this] at hp2)
      omega
    · have h_pc2 : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
        have : n + 2 = n + 1 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_self (n + 1)).mpr (by rwa [this] at hp2)
      omega


lemma primeCounting_add_four_le (n : ℕ) (hn : 10 ≤ n) : Nat.primeCounting (n + 4) ≤ Nat.primeCounting n + 2 := by
  by_cases h_even : n % 2 = 0
  · have hp2 : ¬ (n + 2).Prime := not_prime_of_mod_two_eq_zero (n + 2) (by omega) (by omega)
    have hp4 : ¬ (n + 4).Prime := not_prime_of_mod_two_eq_zero (n + 4) (by omega) (by omega)
    have h_le1 : Nat.primeCounting (n + 1) ≤ Nat.primeCounting n + 1 := by
      by_cases hp1 : (n + 1).Prime
      · have h_eq : Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 := (primeCounting_succ_eq_succ n).mpr hp1
        omega
      · have h_eq : Nat.primeCounting (n + 1) = Nat.primeCounting n := (primeCounting_succ_eq_self n).mpr hp1
        omega
    have h_le2 : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
      have : n + 2 = n + 1 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 1)).mpr hp2
    have h_le3 : Nat.primeCounting (n + 3) ≤ Nat.primeCounting (n + 2) + 1 := by
      by_cases hp3 : (n + 3).Prime
      · have h_eq : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) + 1 := by
          have : n + 3 = n + 2 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_succ (n + 2)).mpr (by rwa [this] at hp3)
        omega
      · have h_eq : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) := by
          have : n + 3 = n + 2 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 2)).mpr (by rwa [this] at hp3)
        omega
    have h_le4 : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) := by
      have : n + 4 = n + 3 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 3)).mpr hp4
    omega
  · have hp1 : ¬ (n + 1).Prime := not_prime_of_mod_two_eq_zero (n + 1) (by omega) (by omega)
    have hp3 : ¬ (n + 3).Prime := not_prime_of_mod_two_eq_zero (n + 3) (by omega) (by omega)
    have h_le1 : Nat.primeCounting (n + 1) = Nat.primeCounting n := (primeCounting_succ_eq_self n).mpr hp1
    have h_le2 : Nat.primeCounting (n + 2) ≤ Nat.primeCounting (n + 1) + 1 := by
      by_cases hp2 : (n + 2).Prime
      · have h_eq : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) + 1 := by
          have : n + 2 = n + 1 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_succ (n + 1)).mpr (by rwa [this] at hp2)
        omega
      · have h_eq : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
          have : n + 2 = n + 1 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 1)).mpr (by rwa [this] at hp2)
        omega
    have h_le3 : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) := by
      have : n + 3 = n + 2 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 2)).mpr (by rwa [this] at hp3)
    have h_le4 : Nat.primeCounting (n + 4) ≤ Nat.primeCounting (n + 3) + 1 := by
      by_cases hp4 : (n + 4).Prime
      · have h_eq : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) + 1 := by
          have : n + 4 = n + 3 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_succ (n + 3)).mpr (by rwa [this] at hp4)
        omega
      · have h_eq : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) := by
          have : n + 4 = n + 3 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 3)).mpr (by rwa [this] at hp4)
        omega
    omega

lemma primeCounting_add_six_le (n : ℕ) (hn : 10 ≤ n) : Nat.primeCounting (n + 6) ≤ Nat.primeCounting n + 2 := by
  by_cases h_even : n % 2 = 0
  · have hp2 : ¬ (n + 2).Prime := not_prime_of_mod_two_eq_zero (n + 2) (by omega) (by omega)
    have hp4 : ¬ (n + 4).Prime := not_prime_of_mod_two_eq_zero (n + 4) (by omega) (by omega)
    have hp6 : ¬ (n + 6).Prime := not_prime_of_mod_two_eq_zero (n + 6) (by omega) (by omega)
    have h_le2 : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
      have : n + 2 = n + 1 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 1)).mpr hp2
    have h_le4 : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) := by
      have : n + 4 = n + 3 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 3)).mpr hp4
    have h_le6 : Nat.primeCounting (n + 6) = Nat.primeCounting (n + 5) := by
      have : n + 6 = n + 5 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 5)).mpr hp6
    by_cases hp1 : (n + 1).Prime
    · have h_le1 : Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 := (primeCounting_succ_eq_succ n).mpr hp1
      by_cases hp3 : (n + 3).Prime
      · have h_le3 : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) + 1 := by
          have : n + 3 = n + 2 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_succ (n + 2)).mpr (by rwa [this] at hp3)
        by_cases hp5 : (n + 5).Prime
        · exfalso
          exact prime_three_consecutive_odds_contradiction n (by omega) hp1 hp3 hp5
        · have h_le5 : Nat.primeCounting (n + 5) = Nat.primeCounting (n + 4) := by
            have : n + 5 = n + 4 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (n + 4)).mpr hp5
          omega
      · have h_le3 : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) := by
          have : n + 3 = n + 2 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 2)).mpr hp3
        have h_le5 : Nat.primeCounting (n + 5) ≤ Nat.primeCounting (n + 4) + 1 := by
          by_cases hp5 : (n + 5).Prime
          · have h_eq : Nat.primeCounting (n + 5) = Nat.primeCounting (n + 4) + 1 := by
              have : n + 5 = n + 4 + 1 := by omega
              rw [this]
              exact (primeCounting_succ_eq_succ (n + 4)).mpr (by rwa [this] at hp5)
            omega
          · have h_eq : Nat.primeCounting (n + 5) = Nat.primeCounting (n + 4) := by
              have : n + 5 = n + 4 + 1 := by omega
              rw [this]
              exact (primeCounting_succ_eq_self (n + 4)).mpr (by rwa [this] at hp5)
            omega
        omega
    · have h_le1 : Nat.primeCounting (n + 1) = Nat.primeCounting n := (primeCounting_succ_eq_self n).mpr hp1
      have h_le3 : Nat.primeCounting (n + 3) ≤ Nat.primeCounting (n + 2) + 1 := by
        by_cases hp3 : (n + 3).Prime
        · have h_eq : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) + 1 := by
            have : n + 3 = n + 2 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_succ (n + 2)).mpr (by rwa [this] at hp3)
          omega
        · have h_eq : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) := by
            have : n + 3 = n + 2 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (n + 2)).mpr (by rwa [this] at hp3)
          omega
      have h_le5 : Nat.primeCounting (n + 5) ≤ Nat.primeCounting (n + 4) + 1 := by
        by_cases hp5 : (n + 5).Prime
        · have h_eq : Nat.primeCounting (n + 5) = Nat.primeCounting (n + 4) + 1 := by
            have : n + 5 = n + 4 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_succ (n + 4)).mpr (by rwa [this] at hp5)
          omega
        · have h_eq : Nat.primeCounting (n + 5) = Nat.primeCounting (n + 4) := by
            have : n + 5 = n + 4 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (n + 4)).mpr (by rwa [this] at hp5)
          omega
      omega
  · have hp1 : ¬ (n + 1).Prime := not_prime_of_mod_two_eq_zero (n + 1) (by omega) (by omega)
    have hp3 : ¬ (n + 3).Prime := not_prime_of_mod_two_eq_zero (n + 3) (by omega) (by omega)
    have hp5 : ¬ (n + 5).Prime := not_prime_of_mod_two_eq_zero (n + 5) (by omega) (by omega)
    have h_le1 : Nat.primeCounting (n + 1) = Nat.primeCounting n := (primeCounting_succ_eq_self n).mpr hp1
    have h_le3 : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) := by
      have : n + 3 = n + 2 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 2)).mpr hp3
    have h_le5 : Nat.primeCounting (n + 5) = Nat.primeCounting (n + 4) := by
      have : n + 5 = n + 4 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 4)).mpr hp5
    by_cases hp2 : (n + 2).Prime
    · have h_le2 : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) + 1 := by
        have : n + 2 = n + 1 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_succ (n + 1)).mpr (by rwa [this] at hp2)
      by_cases hp4 : (n + 4).Prime
      · have h_le4 : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) + 1 := by
          have : n + 4 = n + 3 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_succ (n + 3)).mpr (by rwa [this] at hp4)
        by_cases hp6 : (n + 6).Prime
        · exfalso
          exact prime_three_consecutive_odds_contradiction (n + 1) (by omega) hp2 hp4 hp6
        · have h_le6 : Nat.primeCounting (n + 6) = Nat.primeCounting (n + 5) := by
            have : n + 6 = n + 5 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (n + 5)).mpr hp6
          omega
      · have h_le4 : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) := by
          have : n + 4 = n + 3 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 3)).mpr hp4
        have h_le6 : Nat.primeCounting (n + 6) ≤ Nat.primeCounting (n + 5) + 1 := by
          by_cases hp6 : (n + 6).Prime
          · have h_eq : Nat.primeCounting (n + 6) = Nat.primeCounting (n + 5) + 1 := by
              have : n + 6 = n + 5 + 1 := by omega
              rw [this]
              exact (primeCounting_succ_eq_succ (n + 5)).mpr (by rwa [this] at hp6)
            omega
          · have h_eq : Nat.primeCounting (n + 6) = Nat.primeCounting (n + 5) := by
              have : n + 6 = n + 5 + 1 := by omega
              rw [this]
              exact (primeCounting_succ_eq_self (n + 5)).mpr hp6
            omega
        omega
    · have h_le2 : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
        have : n + 2 = n + 1 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_self (n + 1)).mpr hp2
      have h_le4 : Nat.primeCounting (n + 4) ≤ Nat.primeCounting (n + 3) + 1 := by
        by_cases hp4 : (n + 4).Prime
        · have h_eq : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) + 1 := by
            have : n + 4 = n + 3 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_succ (n + 3)).mpr (by rwa [this] at hp4)
          omega
        · have h_eq : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) := by
            have : n + 4 = n + 3 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (n + 3)).mpr (by rwa [this] at hp4)
          omega
      have h_le6 : Nat.primeCounting (n + 6) ≤ Nat.primeCounting (n + 5) + 1 := by
        by_cases hp6 : (n + 6).Prime
        · have h_eq : Nat.primeCounting (n + 6) = Nat.primeCounting (n + 5) + 1 := by
            have : n + 6 = n + 5 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_succ (n + 5)).mpr (by rwa [this] at hp6)
          omega
        · have h_eq : Nat.primeCounting (n + 6) = Nat.primeCounting (n + 5) := by
            have : n + 6 = n + 5 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (n + 5)).mpr hp6
          omega
      omega

lemma primeCounting_add_eight_le (n : ℕ) (hn : 10 ≤ n) : Nat.primeCounting (n + 8) ≤ Nat.primeCounting n + 3 := by
  have h_six := primeCounting_add_six_le n hn
  by_cases hp7 : (n + 7).Prime
  · have hp8 : ¬ (n + 8).Prime := prime_consecutive_contradiction (n + 6) (by omega) hp7
    have h_le7 : Nat.primeCounting (n + 7) = Nat.primeCounting (n + 6) + 1 := by
      have : n + 7 = n + 6 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_succ (n + 6)).mpr (by rwa [this] at hp7)
    have h_le8 : Nat.primeCounting (n + 8) = Nat.primeCounting (n + 7) := by
      have : n + 8 = n + 7 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 7)).mpr hp8
    omega
  · have h_le7 : Nat.primeCounting (n + 7) = Nat.primeCounting (n + 6) := by
      have : n + 7 = n + 6 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 6)).mpr hp7
    have h_le8 : Nat.primeCounting (n + 8) ≤ Nat.primeCounting (n + 7) + 1 := by
      by_cases hp8 : (n + 8).Prime
      · have h_eq : Nat.primeCounting (n + 8) = Nat.primeCounting (n + 7) + 1 := by
          have : n + 8 = n + 7 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_succ (n + 7)).mpr (by rwa [this] at hp8)
        omega
      · have h_eq : Nat.primeCounting (n + 8) = Nat.primeCounting (n + 7) := by
          have : n + 8 = n + 7 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 7)).mpr (by rwa [this] at hp8)
        omega
    omega

lemma A289827_le_ten_in_set (n : ℕ) (hn : 10 ≤ n) (h_le : A289827 n ≤ 10)
    (h_neq_11 : Nat.primeCounting (11 + n) ≠ Nat.primeCounting 11 + Nat.primeCounting n) :
    A289827 n = 1 ∨ A289827 n = 2 ∨ A289827 n = 4 ∨ A289827 n = 10 := by

  have h_cases : A289827 n = 0 ∨ A289827 n = 1 ∨ A289827 n = 2 ∨ A289827 n = 3 ∨ A289827 n = 4 ∨ A289827 n = 5 ∨ A289827 n = 6 ∨ A289827 n = 7 ∨ A289827 n = 8 ∨ A289827 n = 9 ∨ A289827 n = 10 := by omega
  rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · -- A289827 n = 0: contradiction since m = 1 or 2 or 4 satisfies the condition
    have h_findGreatest_lt_1 : Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n < 1 := by
      change A289827 n < 1
      omega
    have h_not_P1 := Nat.findGreatest_is_greatest h_findGreatest_lt_1 (by omega)
    have h_findGreatest_lt_2 : Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n < 2 := by
      change A289827 n < 2
      omega
    have h_not_P2 := Nat.findGreatest_is_greatest h_findGreatest_lt_2 (by omega)
    have hp1 : (n + 1).Prime := by
      by_contra h_not_prime
      have h_pc1 : Nat.primeCounting (1 + n) = Nat.primeCounting 1 + Nat.primeCounting n := by
        have h_pi_1 : Nat.primeCounting 1 = 0 := by decide
        have h_pc1' : Nat.primeCounting (n + 1) = Nat.primeCounting n := (primeCounting_succ_eq_self n).mpr h_not_prime
        have : 1 + n = n + 1 := by omega
        rw [this, h_pc1', h_pi_1]
        omega
      exact h_not_P1 h_pc1
    have hp2 : (n + 2).Prime := by
      by_contra h_not_prime
      have h_pc2 : Nat.primeCounting (2 + n) = Nat.primeCounting 2 + Nat.primeCounting n := by
        have h_pi_2 : Nat.primeCounting 2 = 1 := by decide
        have h_pc1' : Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 := (primeCounting_succ_eq_succ n).mpr hp1
        have h_pc2' : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
          have : n + 2 = n + 1 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 1)).mpr (by rwa [this] at h_not_prime)
        have : 2 + n = n + 2 := by omega
        rw [this, h_pc2', h_pc1', h_pi_2]
        omega
      exact h_not_P2 h_pc2
    exfalso
    exact prime_consecutive_contradiction n (by omega) hp1 hp2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · -- A289827 n = 3: contradiction
    -- Since A289827 n = 3, we have:
    -- Nat.primeCounting (3 + n) = Nat.primeCounting 3 + Nat.primeCounting n
    -- Nat.primeCounting 3 = 2. So:
    -- Nat.primeCounting (3 + n) = Nat.primeCounting n + 2
    -- Let us use the successor relation to show this is impossible!
    -- Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) + (1 or 0)
    -- = Nat.primeCounting (n + 1) + (1 or 0) + (1 or 0)
    -- = Nat.primeCounting n + (1 or 0) + (1 or 0) + (1 or 0)
    -- If the sum is + 2, then we must have two of them being 1, which means we have at least two primes among {n+1, n+2, n+3}.
    -- Since n >= 10, the elements are >= 11, so we cannot have consecutive primes or other prime clusters that are impossible.
    -- Let us write this using prime_consecutive_contradiction!
    have h_eq : Nat.primeCounting (3 + n) = Nat.primeCounting 3 + Nat.primeCounting n := Nat.findGreatest_of_ne_zero (P := fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) h3 (by omega)
    have h_pi_3 : Nat.primeCounting 3 = 2 := by decide
    rw [h_pi_3] at h_eq
    have h_pc3 : Nat.primeCounting (n + 3) = Nat.primeCounting n + 2 := by
      have : 3 + n = n + 3 := by omega
      rw [← this]
      omega
    -- Let us write down the chain of successor values
    -- Nat.primeCounting (n + 3) is either Nat.primeCounting (n + 2) or Nat.primeCounting (n + 2) + 1
    by_cases hp3 : (n + 3).Prime
    · have h_pc3' : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) + 1 := by
        have : n + 3 = n + 2 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_succ (n + 2)).mpr (by rwa [this] at hp3)
      by_cases hp2 : (n + 2).Prime
      · -- both n+2 and n+3 are prime. Contradiction!
        exfalso
        exact prime_consecutive_contradiction (n + 1) (by omega) hp2 hp3
      · have h_pc2' : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
          have : n + 2 = n + 1 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 1)).mpr (by rwa [this] at hp2)
        by_cases hp1 : (n + 1).Prime
        · have h_pc1' : Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 := by
            have : n + 1 = n + 1 := rfl
            exact (primeCounting_succ_eq_succ n).mpr hp1
          -- Then Nat.primeCounting (n + 3) = (Nat.primeCounting n + 1) + 1 = Nat.primeCounting n + 2.
          -- This is possible! But wait, if both n+1 and n+3 are prime, that is twin primes, which is possible.
          -- But wait! If A289827 n = 3, then it is NOT the largest.
          -- If n+1 and n+3 are prime, then n+4 is composite because it is even.
          have hp4 : ¬ (n + 4).Prime := by
            have h_odd3 : (n + 3) % 2 = 1 := hp3.eq_two_or_odd.resolve_left (by omega)
            have h_even4 : Even (n + 4) := by
              have : (n + 4) % 2 = 0 := by omega
              exact Nat.even_iff.mpr this
            intro hp4_prime
            have h_eq4 : n + 4 = 2 := hp4_prime.even_iff.mp h_even4
            omega
          have h_pc4 : Nat.primeCounting (n + 4) = Nat.primeCounting (n + 3) := by
            have : n + 4 = n + 3 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (n + 3)).mpr hp4
          -- So Nat.primeCounting (4 + n) = Nat.primeCounting 4 + Nat.primeCounting n
          have h_pc4' : Nat.primeCounting (4 + n) = Nat.primeCounting 4 + Nat.primeCounting n := by
            have h_pi_4 : Nat.primeCounting 4 = 2 := by decide
            have : 4 + n = n + 4 := by omega
            rw [this, h_pc4, h_pc3, h_pi_4]
            omega
          -- This contradicts A289827 n = 3 being the largest!
          -- findGreatest_is_greatest says ¬ P 4 because 3 < 4 <= n
          have h_findGreatest_lt_4 : Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n < 4 := by
            change A289827 n < 4
            omega
          have h_not_P4 := Nat.findGreatest_is_greatest h_findGreatest_lt_4 (by omega)
          exact False.elim (h_not_P4 h_pc4')
        · have h_pc1' : Nat.primeCounting (n + 1) = Nat.primeCounting n := by
            exact (primeCounting_succ_eq_self n).mpr hp1
          -- Then Nat.primeCounting (n + 3) = Nat.primeCounting n + 1. But h_pc3 says it is + 2. Contradiction!
          omega
    · have h_pc3' : Nat.primeCounting (n + 3) = Nat.primeCounting (n + 2) := by
        have : n + 3 = n + 2 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_self (n + 2)).mpr (by rwa [this] at hp3)
      -- Then Nat.primeCounting (n + 3) can be at most Nat.primeCounting n + 2, but since n + 3 is not prime,
      -- it can be at most Nat.primeCounting n + 1.
      -- Let us check: Nat.primeCounting (n + 2) <= Nat.primeCounting (n + 1) + 1 <= Nat.primeCounting n + 2.
      -- If it is equal to Nat.primeCounting n + 2, then we must have both n+1 and n+2 are prime.
      -- But both n+1 and n+2 are prime is a contradiction!
      by_cases hp2 : (n + 2).Prime
      · have h_pc2' : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) + 1 := by
          have : n + 2 = n + 1 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_succ (n + 1)).mpr (by rwa [this] at hp2)
        by_cases hp1 : (n + 1).Prime
        · exfalso
          exact prime_consecutive_contradiction n (by omega) hp1 hp2
        · have h_pc1' : Nat.primeCounting (n + 1) = Nat.primeCounting n := by
            exact (primeCounting_succ_eq_self n).mpr hp1
          omega
      · have h_pc2' : Nat.primeCounting (n + 2) = Nat.primeCounting (n + 1) := by
          have : n + 2 = n + 1 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 1)).mpr (by rwa [this] at hp2)
        -- Then Nat.primeCounting (n+3) = Nat.primeCounting (n+1) <= Nat.primeCounting n + 1.
        -- But h_pc3 says it is equal to Nat.primeCounting n + 2. Contradiction!
        have h_le_n1 : Nat.primeCounting (n + 1) ≤ Nat.primeCounting n + 1 := by
          by_cases hp1 : (n + 1).Prime
          · rw [(primeCounting_succ_eq_succ n).mpr hp1]
          · rw [(primeCounting_succ_eq_self n).mpr hp1]
            omega
        omega
  · exact Or.inr (Or.inr (Or.inl h4))
  · -- A289827 n = 5: contradiction
    have h_eq : Nat.primeCounting (5 + n) = Nat.primeCounting 5 + Nat.primeCounting n := Nat.findGreatest_of_ne_zero (P := fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) h5 (by omega)
    have h_pi_5 : Nat.primeCounting 5 = 3 := by decide
    have h_pc5 : Nat.primeCounting (n + 5) = Nat.primeCounting n + 3 := by
      have : 5 + n = n + 5 := by omega
      rw [this] at h_eq
      omega
    have h_six_le := primeCounting_add_six_le n hn
    have h_le5 : Nat.primeCounting (n + 5) ≤ Nat.primeCounting (n + 6) := primeCounting_le_succ (n + 5)
    omega
  · -- A289827 n = 6: contradiction
    have h_eq : Nat.primeCounting (6 + n) = Nat.primeCounting 6 + Nat.primeCounting n := Nat.findGreatest_of_ne_zero (P := fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) h6 (by omega)
    have h_pi_6 : Nat.primeCounting 6 = 3 := by decide
    have h_pc6 : Nat.primeCounting (n + 6) = Nat.primeCounting n + 3 := by
      have : 6 + n = n + 6 := by omega
      rw [this] at h_eq
      omega
    have h_six_le := primeCounting_add_six_le n hn
    omega
  · -- A289827 n = 7: contradiction
    have h_eq : Nat.primeCounting (7 + n) = Nat.primeCounting 7 + Nat.primeCounting n := Nat.findGreatest_of_ne_zero (P := fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) h7 (by omega)
    have h_pi_7 : Nat.primeCounting 7 = 4 := by decide
    have h_pc7 : Nat.primeCounting (n + 7) = Nat.primeCounting n + 4 := by
      have : 7 + n = n + 7 := by omega
      rw [this] at h_eq
      omega
    have h_eight_le := primeCounting_add_eight_le n hn
    have h_le7 : Nat.primeCounting (n + 7) ≤ Nat.primeCounting (n + 8) := primeCounting_le_succ (n + 7)
    omega
  · -- A289827 n = 8: contradiction
    have h_eq : Nat.primeCounting (8 + n) = Nat.primeCounting 8 + Nat.primeCounting n := Nat.findGreatest_of_ne_zero (P := fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) h8 (by omega)
    have h_pi_8 : Nat.primeCounting 8 = 4 := by decide
    have h_pc8 : Nat.primeCounting (n + 8) = Nat.primeCounting n + 4 := by
      have : 8 + n = n + 8 := by omega
      rw [this] at h_eq
      omega
    have h_eight_le := primeCounting_add_eight_le n hn
    omega
  · -- A289827 n = 9: contradiction
    have h_eq : Nat.primeCounting (9 + n) = Nat.primeCounting 9 + Nat.primeCounting n := Nat.findGreatest_of_ne_zero (P := fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) h9 (by omega)
    have h_pi_9 : Nat.primeCounting 9 = 4 := by decide
    have h_pc9 : Nat.primeCounting (n + 9) = Nat.primeCounting n + 4 := by
      have : 9 + n = n + 9 := by omega
      rw [this] at h_eq
      omega
    have hp10 : ¬ (n + 10).Prime := by
      intro hp10_prime
      by_cases h_even : n % 2 = 0
      · have h_not_prime : ¬ (n + 10).Prime := not_prime_of_mod_two_eq_zero (n + 10) (by omega) (by omega)
        exact h_not_prime hp10_prime
      · have hp9 : ¬ (n + 9).Prime := not_prime_of_mod_two_eq_zero (n + 9) (by omega) (by omega)
        have h_pc9_eq8 : Nat.primeCounting (n + 9) = Nat.primeCounting (n + 8) := by
          have : n + 9 = n + 8 + 1 := by omega
          rw [this]
          exact (primeCounting_succ_eq_self (n + 8)).mpr hp9
        have h_eight_le := primeCounting_add_eight_le n hn
        omega
    have h_pc10 : Nat.primeCounting (n + 10) = Nat.primeCounting (n + 9) := by
      have : n + 10 = n + 9 + 1 := by omega
      rw [this]
      exact (primeCounting_succ_eq_self (n + 9)).mpr hp10
    have h_pc10' : Nat.primeCounting (10 + n) = Nat.primeCounting 10 + Nat.primeCounting n := by
      have h_pi_10 : Nat.primeCounting 10 = 4 := by decide
      have : 10 + n = n + 10 := by omega
      rw [this, h_pc10, h_pc9, h_pi_10]
      omega
    have h_findGreatest_lt_10 : Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n < 10 := by
      change A289827 n < 10
      omega
    have h_not_P10 := Nat.findGreatest_is_greatest h_findGreatest_lt_10 (by omega)
    exact False.elim (h_not_P10 h_pc10')
  · exact Or.inr (Or.inr (Or.inr h10))

lemma primeCounting_add_lt (n : ℕ) (hn : 10 ≤ n) (m : ℕ) (hm1 : 11 ≤ m) (hm2 : m ≤ n) :
    Nat.primeCounting (m + n) < Nat.primeCounting m + Nat.primeCounting n := by
  induction' m with m ih
  · omega
  · by_cases h_eq : m = 10
    · subst h_eq
      exact primeCounting_add_eleven n hn
    · have hm1' : 11 ≤ m := by omega
      have hm2' : m ≤ n := by omega
      have h_ih := ih hm1' hm2'
      by_cases hp1 : (m + 1).Prime
      · have h_pc1 : Nat.primeCounting (m + 1) = Nat.primeCounting m + 1 := (primeCounting_succ_eq_succ m).mpr hp1
        have h_pc2 : Nat.primeCounting (m + 1 + n) ≤ Nat.primeCounting (m + n) + 1 := by
          have : m + 1 + n = m + n + 1 := by omega
          rw [this]
          exact primeCounting_succ_le (m + n)
        omega
      · have h_pc1 : Nat.primeCounting (m + 1) = Nat.primeCounting m := (primeCounting_succ_eq_self m).mpr hp1
        by_cases hp2 : (m + 1 + n).Prime
        · have h_pc2 : Nat.primeCounting (m + 1 + n) = Nat.primeCounting (m + n) + 1 := by
            have : m + 1 + n = m + n + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_succ (m + n)).mpr (by rwa [this] at hp2)
          sorry
        · have h_pc2 : Nat.primeCounting (m + 1 + n) = Nat.primeCounting (m + n) := by
            have : m + 1 + n = m + n + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (m + n)).mpr (by rwa [this] at hp2)
          omega


theorem oeis_289827_conjecture_0 (n : ℕ) (hn : 1 < n) :
    A289827 n = 1 ∨ A289827 n = 2 ∨ A289827 n = 4 ∨ A289827 n = 10 := by
  by_cases h10 : n ≤ 10
  · interval_cases n
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · have h_gt : 10 ≤ n := by omega
    have h_neq : ∀ m, 11 ≤ m → m ≤ n → Nat.primeCounting (m + n) ≠ Nat.primeCounting m + Nat.primeCounting n := by
      sorry
    have h_le := findGreatest_le_ten n h_gt h_neq
    have h_neq_11 : Nat.primeCounting (11 + n) ≠ Nat.primeCounting 11 + Nat.primeCounting n := ne_of_lt (primeCounting_add_eleven n h_gt)
    exact A289827_le_ten_in_set n h_gt h_le h_neq_11







