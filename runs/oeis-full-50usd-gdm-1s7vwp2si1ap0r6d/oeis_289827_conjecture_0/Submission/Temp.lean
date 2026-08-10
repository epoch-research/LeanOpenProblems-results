import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

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

lemma primeCounting_add_twelve (n : ℕ) (hn : 10 ≤ n) :
    Nat.primeCounting (12 + n) < Nat.primeCounting 12 + Nat.primeCounting n := by
  have h1 : Nat.primeCounting (12 + n) = Nat.primeCounting (n + 6 + 6) := by congr 1; omega
  have h2 : Nat.primeCounting (12 + n) ≤ Nat.primeCounting n + 4 := by
    rw [h1]
    have h3 := primeCounting_add_six_le (n + 6) (by omega)
    have h4 := primeCounting_add_six_le n hn
    omega
  have h5 : Nat.primeCounting 12 = 5 := rfl
  omega


lemma primeCounting_succ_eq_succ (n : ℕ) : Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 ↔ (n + 1).Prime := by
  rw [Nat.primeCounting, Nat.primeCounting]
  have h1 : n + 1 + 1 = n + 2 := by omega
  have h2 : n + 1 = n + 1 := rfl
  rw [h1, h2]
  exact Nat.count_succ_eq_succ_count_iff

lemma primeCounting_succ_eq_self (n : ℕ) : Nat.primeCounting (n + 1) = Nat.primeCounting n ↔ ¬ (n + 1).Prime := by
  rw [Nat.primeCounting, Nat.primeCounting]
  have h1 : n + 1 + 1 = n + 2 := by omega
  have h2 : n + 1 = n + 1 := rfl
  rw [h1, h2]
  exact Nat.count_succ_eq_count_iff

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

lemma prime_consecutive_contradiction (n : ℕ) (hn : 2 < n) (hp1 : (n + 1).Prime) (hp2 : (n + 2).Prime) : False := by
  have h_even_or_odd := Nat.even_or_odd (n + 1)
  rcases h_even_or_odd with h_even | h_odd
  · have h_eq : n + 1 = 2 := hp1.even_iff.mp h_even
    omega
  · have h_even2 : (n + 2) % 2 = 0 := by
      have : (n + 1) % 2 = 1 := Nat.odd_iff.mp h_odd
      omega
    have h_even2' : Even (n + 2) := Nat.even_iff.mpr h_even2
    have h_eq2 : n + 2 = 2 := hp2.even_iff.mp h_even2'
    omega

lemma not_prime_of_mod_two_eq_zero (x : ℕ) (h_mod : x % 2 = 0) (h_gt : 2 < x) : ¬ x.Prime := by
  intro hp
  have h_even : Even x := Nat.even_iff.mpr h_mod
  have h_eq : x = 2 := hp.even_iff.mp h_even
  omega

lemma primeCounting_add_lt (n : ℕ) (hn : 10 ≤ n) (m : ℕ) (hm1 : 11 ≤ m) (hm2 : m ≤ n) :
    Nat.primeCounting (m + n) < Nat.primeCounting m + Nat.primeCounting n := by
  induction' m using Nat.strong_induction_on with m ih
  by_cases h11 : m = 11
  · subst h11
    exact primeCounting_add_eleven n hn
  by_cases h12 : m = 12
  · subst h12
    exact primeCounting_add_twelve n hn
  · have hm1_gt : 12 < m := by omega
    have hm_sub1 : 11 ≤ m - 1 := by omega
    have hm_sub2 : m - 1 ≤ n := by omega
    by_cases hp1 : m.Prime
    · have h_ih := ih (m - 1) (by omega) hm_sub1 hm_sub2
      have h_pc1 : Nat.primeCounting m = Nat.primeCounting (m - 1) + 1 := by
        have : m = m - 1 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_succ (m - 1)).mpr (by rwa [← this])
      have h_le : Nat.primeCounting (m + n) ≤ Nat.primeCounting (m - 1 + n) + 1 := by
        have : m + n = m - 1 + n + 1 := by omega
        rw [this]
        exact primeCounting_succ_le (m - 1 + n)
      omega
    · have h_ih := ih (m - 1) (by omega) hm_sub1 hm_sub2
      have h_pc1 : Nat.primeCounting m = Nat.primeCounting (m - 1) := by
        have : m = m - 1 + 1 := by omega
        rw [this]
        exact (primeCounting_succ_eq_self (m - 1)).mpr (by rwa [← this])
      by_cases hp2 : (m - 1).Prime
      · by_cases hp3 : (m + n).Prime
        · have h_comp : ¬ (m - 1 + n).Prime := by
            have h_even : (m - 1 + n) % 2 = 0 := by
              have hp2_odd : (m - 1) % 2 = 1 := by
                have : m - 1 ≥ 11 := by omega
                exact Nat.Prime.eq_two_or_odd hp2 |>.resolve_left (by omega)
              have hp3_odd : (m + n) % 2 = 1 := by
                have : m + n ≥ 22 := by omega
                exact Nat.Prime.eq_two_or_odd hp3 |>.resolve_left (by omega)
              omega
            have h_gt : 2 < m - 1 + n := by omega
            exact not_prime_of_mod_two_eq_zero (m - 1 + n) h_even h_gt
          have h_pc2 : Nat.primeCounting (m - 1 + n) = Nat.primeCounting (m - 2 + n) := by
            have : m - 1 + n = m - 2 + n + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (m - 2 + n)).mpr (by rwa [← this])
          have h_ih2 := ih (m - 2) (by omega) (by omega) (by omega)
          have h_pc3 : Nat.primeCounting (m - 1) = Nat.primeCounting (m - 2) + 1 := by
            have : m - 1 = m - 2 + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_succ (m - 2)).mpr (by rwa [← this])
          have h_le : Nat.primeCounting (m + n) = Nat.primeCounting (m - 1 + n) + 1 := by
            have : m + n = m - 1 + n + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_succ (m - 1 + n)).mpr (by rwa [← this])
          omega
        · have h_pc2 : Nat.primeCounting (m + n) = Nat.primeCounting (m - 1 + n) := by
            have : m + n = m - 1 + n + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (m - 1 + n)).mpr (by rwa [← this])
          omega
      · by_cases hp3 : (m + n).Prime
        · by_cases hp4 : (m - 1 + n).Prime
          · exfalso
            exact prime_consecutive_contradiction (m - 2 + n) (by omega) hp4 hp3
          · have h_pc2 : Nat.primeCounting (m - 1 + n) = Nat.primeCounting (m - 2 + n) := by
              have : m - 1 + n = m - 2 + n + 1 := by omega
              rw [this]
              exact (primeCounting_succ_eq_self (m - 2 + n)).mpr (by rwa [← this])
            have h_pc3 : Nat.primeCounting (m - 1) = Nat.primeCounting (m - 2) := by
              have : m - 1 = m - 2 + 1 := by omega
              rw [this]
              exact (primeCounting_succ_eq_self (m - 2)).mpr (by rwa [← this])
            have h_ih2 := ih (m - 2) (by omega) (by omega) (by omega)
            omega
        · have h_pc2 : Nat.primeCounting (m + n) = Nat.primeCounting (m - 1 + n) := by
            have : m + n = m - 1 + n + 1 := by omega
            rw [this]
            exact (primeCounting_succ_eq_self (m - 1 + n)).mpr (by rwa [← this])
          omega
