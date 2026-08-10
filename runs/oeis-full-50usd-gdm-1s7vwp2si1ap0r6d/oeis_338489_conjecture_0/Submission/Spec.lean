import FormalConjectures.Util.ProblemImports
open Nat Int

/--
A338489: Let $t$ be the closest triangular number to $n!$ (in case $n=2$, the only case where we have a tie, take the larger $t$); then $a(n) = n! - t$.
-/
def a (n : ℕ) : ℤ :=
  -- T(k) is the k-th triangular number k * (k + 1) / 2
  let T (k : ℕ) : ℕ := k * (k + 1) / 2
  let N_nat := n.factorial

  -- The index $k_0$ such that $T_{k_0} \le N! < T_{k_0+1}$
  -- $k_0 = \lfloor (\sqrt{8 \cdot N! + 1} - 1) / 2 \rfloor$.
  -- We use Nat.sqrt, which computes the floor of the square root.
  let k0_numerator : ℕ := (8 * N_nat + 1).sqrt.pred
  let k0 : ℕ := k0_numerator / 2

  let T_k0_nat := T k0
  let T_k1_nat := T (k0 + 1)

  let N : ℤ := N_nat
  let T_k0 : ℤ := T_k0_nat
  let T_k1 : ℤ := T_k1_nat

  -- Calculate distances. Int.abs is used.
  let d0 := abs (N - T_k0)
  let d1 := abs (N - T_k1)

  -- Determine the closest triangular number t
  let t : ℤ :=
    if d0 < d1 then
      T_k0
    else if d1 < d0 then
      T_k1
    else -- d0 = d1, a tie
      if n = 2 then
        -- Tie-breaker for n=2: take the larger t
        max T_k0 T_k1
      else
        -- For other ties, T_k0 is an arbitrary selection.
        -- However, the sequence definition states n=2 is the *only* case for a tie.
        T_k0

  N - t

/-- A natural number is triangular if it is of the form $k(k+1)/2$ for some natural number $k$. -/
def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

def is_triangular_dec (x : ℕ) : Bool :=
  (List.range (2 * x + 2)).any (fun k => x == k * (k + 1) / 2)

lemma is_triangular_iff_dec (x : ℕ) : is_triangular x ↔ is_triangular_dec x = true := by
  constructor
  · rintro ⟨k, hk⟩
    have hk_le : k ≤ 2 * x + 1 := by
      rcases k with _ | k
      · omega
      · have h_pos : 0 < k + 1 := by omega
        have h1 : k + 1 ≤ (k + 1) * (k + 2) / 2 := by
          have h_mul : 2 * (k + 1) ≤ (k + 1) * (k + 2) := by
            calc 2 * (k + 1) ≤ (k + 2) * (k + 1) := Nat.mul_le_mul_right (k + 1) (by omega)
              _ = (k + 1) * (k + 2) := Nat.mul_comm _ _
          omega
        rw [← hk] at h1
        omega
    rw [is_triangular_dec, List.any_eq_true]
    use k
    constructor
    · rw [List.mem_range]; omega
    · rw [beq_iff_eq]; exact hk
  · rw [is_triangular_dec, List.any_eq_true]
    rintro ⟨k, _, hk⟩
    rw [beq_iff_eq] at hk
    exact ⟨k, hk⟩

lemma k_mul_k_add_one_even (k : ℕ) : 2 ∣ k * (k + 1) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · use m * (2 * m + 1)
    ring
  · use (2 * m + 1) * (m + 1)
    ring

lemma k_mul_k_add_one_div_two_mul_two (k : ℕ) : (k * (k + 1) / 2) * 2 = k * (k + 1) := by
  have hdvd : 2 ∣ k * (k + 1) := k_mul_k_add_one_even k
  exact Nat.div_mul_cancel hdvd

lemma not_triangular_of_not_square (x : ℕ) (h : ¬ ∃ y : ℕ, y * y = 8 * x + 1) : ¬ is_triangular x := by
  rintro ⟨k, rfl⟩
  apply h
  use 2 * k + 1
  have : 8 * (k * (k + 1) / 2) + 1 = (2 * k + 1) * (2 * k + 1) := by
    have : 8 * (k * (k + 1) / 2) = 4 * ((k * (k + 1) / 2) * 2) := by ring
    rw [this, k_mul_k_add_one_div_two_mul_two]
    ring
  exact this.symm

lemma not_square_of_not_square_zmod (x : ℕ) (p : ℕ) [Fact (Nat.Prime p)] (h : ¬ ∃ y : ZMod p, y^2 = (x : ZMod p)) :
  ¬ ∃ y : ℕ, y * y = x := by
  rintro ⟨y, hy⟩
  apply h
  use (y : ZMod p)
  have : ((y : ZMod p) ^ 2) = (((y * y : ℕ) : ZMod p)) := by
    simp only [sq, Nat.cast_mul]
  rw [this, hy]

instance instPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
instance instPrime13 : Fact (Nat.Prime 13) := ⟨by decide⟩
instance instPrime17 : Fact (Nat.Prime 17) := ⟨by decide⟩
instance instPrime19 : Fact (Nat.Prime 19) := ⟨by decide⟩
instance instPrime23 : Fact (Nat.Prime 23) := ⟨by decide⟩
instance instPrime29 : Fact (Nat.Prime 29) := ⟨by decide⟩
instance instPrime31 : Fact (Nat.Prime 31) := ⟨by decide⟩
instance instPrime37 : Fact (Nat.Prime 37) := ⟨by decide⟩
instance instPrime41 : Fact (Nat.Prime 41) := ⟨by decide⟩
instance instPrime47 : Fact (Nat.Prime 47) := ⟨by decide⟩
instance instPrime61 : Fact (Nat.Prime 61) := ⟨by decide⟩
instance instPrime53 : Fact (Nat.Prime 53) := ⟨by decide⟩
instance instPrime59 : Fact (Nat.Prime 59) := ⟨by decide⟩
instance instPrime71 : Fact (Nat.Prime 71) := ⟨by decide⟩
instance instPrime89 : Fact (Nat.Prime 89) := ⟨by decide⟩
instance instPrime73 : Fact (Nat.Prime 73) := ⟨by decide⟩
instance instPrime79 : Fact (Nat.Prime 79) := ⟨by decide⟩

lemma exists_prime_div_factorial (n : ℕ) (hn : 6 ≤ n) : ∃ p, Nat.Prime p ∧ n / 2 < p ∧ p ≤ n := by
  have h_pos : n / 2 ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) h_pos
  use p
  refine ⟨hp_prime, hp1, ?_⟩
  have h_le : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  exact hp2.trans h_le


lemma factorial_gt_quadratic {n : ℕ} (hn : 4 ≤ n) : 2 * n.factorial > n * (n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_mul : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_mul]
    have h1 : 2 * m.factorial > m * (m + 1) := ih
    have h2 : (m + 1) * (2 * m.factorial) > (m + 1) * (m * (m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left h1 (by omega)
    have h3 : m * (m + 1) ≥ m + 2 := by
      calc m * (m + 1) ≥ 4 * (m + 1) := Nat.mul_le_mul_right (m + 1) hm
        _ = 4 * m + 4 := by ring
        _ ≥ m + 2 := by omega
    have h4 : (m + 1) * (m * (m + 1)) ≥ (m + 1) * (m + 2) := Nat.mul_le_mul_left (m + 1) h3
    exact lt_of_le_of_lt h4 h2

lemma factorial_gt_two_n_mul {n : ℕ} (hn : 5 ≤ n) : 2 * n.factorial ≥ 2 * n * (2 * n - 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial ≥ 2 * m * (2 * m - 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) ≥ (m + 1) * (2 * m * (2 * m - 1)) := Nat.mul_le_mul_left (m + 1) ih'
    have h2 : (m + 1) * (2 * m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * (m + 1) - 1) := by
      have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [this]
      have h3 : m * (2 * m - 1) ≥ 2 * m + 1 := by
        have h_sub : m * (2 * m - 1) = 2 * m * m - m := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          congr 1
          ring
        rw [h_sub]
        have h_quad : 2 * m * m ≥ 10 * m := by
          calc 2 * m * m = (2 * m) * m := by ring
            _ ≥ (2 * 5) * m := Nat.mul_le_mul_right m (by omega)
            _ = 10 * m := by ring
        omega
      have h4 : 2 * (m + 1) * (m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * m + 1) := Nat.mul_le_mul_left (2 * (m + 1)) h3
      have h_comm : (m + 1) * (2 * m * (2 * m - 1)) = 2 * (m + 1) * (m * (2 * m - 1)) := by ring
      rw [h_comm]
      exact h4
    exact le_trans h2 h1

lemma k_ge_two_n {n k : ℕ} (h_eq : 2 * n.factorial = k * (k + 1)) (hn : 5 ≤ n) : k + 1 ≥ 2 * n := by
  by_contra hc
  have hk : k + 1 < 2 * n := by omega
  have hk2 : k < 2 * n - 1 := by omega
  have h_lt : k * (k + 1) < 2 * n * (2 * n - 1) := by
    have h1 : k * (k + 1) < (2 * n - 1) * (k + 1) := by
      exact mul_lt_mul_of_pos_right hk2 (by omega)
    have h2 : (2 * n - 1) * (k + 1) < (2 * n - 1) * (2 * n) := by
      exact mul_lt_mul_of_pos_left hk (by omega)
    have h3 : k * (k + 1) < (2 * n - 1) * (2 * n) := lt_trans h1 h2
    rwa [Nat.mul_comm (2 * n - 1) (2 * n)] at h3
  have h_ge : 2 * n.factorial ≥ 2 * n * (2 * n - 1) := factorial_gt_two_n_mul hn
  omega

lemma k_ge_two_p {n k p : ℕ} (h_eq : 2 * n.factorial = k * (k + 1))
    (hp_prime : Nat.Prime p) (_hp_gt : n / 2 < p) (hp_le : p ≤ n) (hn : 67 ≤ n) :
    k + 1 ≥ 2 * p := by
  have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  have hp_dvd_two_fact : p ∣ 2 * n.factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
  rw [h_eq] at hp_dvd_two_fact
  cases' Nat.Prime.dvd_mul hp_prime |>.mp hp_dvd_two_fact with hpk hpk1
  · obtain ⟨d, hd⟩ := hpk
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    rcases eq_or_ne d 1 with rfl | hd_ne
    · have hkp : k = p := by omega
      rw [hkp] at h_eq
      have hp_le_fact : p * (p + 1) ≤ n * (n + 1) := Nat.mul_le_mul hp_le (by omega)
      have h_gt : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
      omega
    · have hd_ge_2 : d ≥ 2 := by omega
      have hk_ge : k ≥ 2 * p := by
        calc k = p * d := hd
          _ ≥ p * 2 := Nat.mul_le_mul_left p hd_ge_2
          _ = 2 * p := by ring
      omega
  · obtain ⟨d, hd⟩ := hpk1
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    rcases eq_or_ne d 1 with rfl | hd_ne
    · have hkp : k + 1 = p := by omega
      have hk_eq : k = p - 1 := by omega
      rw [hk_eq] at h_eq
      have hp_eq : p - 1 + 1 = p := by omega
      rw [hp_eq] at h_eq
      have hp_le_fact : (p - 1) * p ≤ (n - 1) * n := by
        have h_p_pos : p > 0 := Nat.Prime.pos hp_prime
        have h_sub : p - 1 ≤ n - 1 := by omega
        exact Nat.mul_le_mul h_sub hp_le
      have h_gt : 2 * n.factorial > n * (n - 1) := by
        have h_gt_quad : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
        have h_quad_le : n * (n + 1) ≥ (n - 1) * n := by
          have : n + 1 ≥ n - 1 := by omega
          have h_mul_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
          rw [h_mul_comm]
          exact Nat.mul_le_mul_left n this
        omega
      have h_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
      rw [h_comm] at hp_le_fact
      omega
    · have hd_ge_2 : d ≥ 2 := by omega
      calc k + 1 = p * d := hd
        _ ≥ p * 2 := Nat.mul_le_mul_left p hd_ge_2
        _ = 2 * p := by ring

lemma factorial_gt_two_n_mul_two_n_plus_one {n : ℕ} (hn : 5 ≤ n) : 2 * n.factorial > 2 * n * (2 * n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial > 2 * m * (2 * m + 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) > (m + 1) * (2 * m * (2 * m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left ih' (by omega)
    have h2 : (m + 1) * (2 * m * (2 * m + 1)) ≥ 2 * (m + 1) * (2 * (m + 1) + 1) := by
      have : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
      rw [this]
      have h3 : m * (2 * m + 1) ≥ 2 * m + 3 := by
        have h_mul : m * (2 * m + 1) = 2 * m * m + m := by ring
        rw [h_mul]
        have h_quad : 2 * m * m ≥ 10 * m := by
          calc 2 * m * m = (2 * m) * m := by ring
            _ ≥ (2 * 5) * m := Nat.mul_le_mul_right m (by omega)
            _ = 10 * m := by ring
        omega
      have h4 : 2 * (m + 1) * (m * (2 * m + 1)) ≥ 2 * (m + 1) * (2 * m + 3) := Nat.mul_le_mul_left (2 * (m + 1)) h3
      have h_comm : (m + 1) * (2 * m * (2 * m + 1)) = 2 * (m + 1) * (m * (2 * m + 1)) := by ring
      rw [h_comm]
      exact h4
    exact lt_of_le_of_lt h2 h1

lemma k_ge_three_p {n k p : ℕ} (h_eq : 2 * n.factorial = k * (k + 1))
    (hp_prime : Nat.Prime p) (_hp_gt : n / 2 < p) (hp_le : p ≤ n) (hn : 5 ≤ n) :
    k + 1 ≥ 3 * p := by
  have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  have hp_dvd_two_fact : p ∣ 2 * n.factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
  rw [h_eq] at hp_dvd_two_fact
  cases' Nat.Prime.dvd_mul hp_prime |>.mp hp_dvd_two_fact with hpk hpk1
  · obtain ⟨d, hd⟩ := hpk
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    rcases lt_or_ge d 3 with hd_lt | hd_ge_3
    · interval_cases d
      · -- d = 1
        have hkp : k = p := by omega
        rw [hkp] at h_eq
        have hp_le_fact : p * (p + 1) ≤ n * (n + 1) := Nat.mul_le_mul hp_le (by omega)
        have h_gt : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
        omega
      · -- d = 2
        have hkp : k = 2 * p := by omega
        rw [hkp] at h_eq
        have hp_le_fact : 2 * p * (2 * p + 1) ≤ 2 * n * (2 * n + 1) := by
          have h2p : 2 * p ≤ 2 * n := by omega
          have h2p1 : 2 * p + 1 ≤ 2 * n + 1 := by omega
          exact Nat.mul_le_mul h2p h2p1
        have h_gt : 2 * n.factorial > 2 * n * (2 * n + 1) := factorial_gt_two_n_mul_two_n_plus_one (by omega)
        omega
    · have hk_ge : k ≥ 3 * p := by
        calc k = p * d := hd
          _ ≥ p * 3 := Nat.mul_le_mul_left p hd_ge_3
          _ = 3 * p := by ring
      omega
  · obtain ⟨d, hd⟩ := hpk1
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    rcases lt_or_ge d 3 with hd_lt | hd_ge_3
    · interval_cases d
      · -- d = 1
        have hkp : k + 1 = p := by omega
        have hk_eq : k = p - 1 := by omega
        rw [hk_eq] at h_eq
        have hp_eq : p - 1 + 1 = p := by omega
        rw [hp_eq] at h_eq
        have hp_le_fact : (p - 1) * p ≤ (n - 1) * n := by
          have h_p_pos : p > 0 := Nat.Prime.pos hp_prime
          have h_sub : p - 1 ≤ n - 1 := by omega
          exact Nat.mul_le_mul h_sub hp_le
        have h_gt : 2 * n.factorial > n * (n - 1) := by
          have h_gt_quad : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
          have h_quad_le : n * (n + 1) ≥ (n - 1) * n := by
            have : n + 1 ≥ n - 1 := by omega
            have h_mul_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
            rw [h_mul_comm]
            exact Nat.mul_le_mul_left n this
          omega
        have h_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
        rw [h_comm] at hp_le_fact
        omega
      · -- d = 2
        have hkp : k + 1 = 2 * p := by omega
        have hk_eq : k = 2 * p - 1 := by omega
        rw [hk_eq] at h_eq
        have hp_eq : 2 * p - 1 + 1 = 2 * p := by omega
        rw [hp_eq] at h_eq
        have hp_le_fact : (2 * p - 1) * (2 * p) ≤ (2 * n - 1) * (2 * n) := by
          have h_sub : 2 * p - 1 ≤ 2 * n - 1 := by omega
          have h_le_2p : 2 * p ≤ 2 * n := by omega
          exact Nat.mul_le_mul h_sub h_le_2p
        have h_gt : 2 * n.factorial > (2 * n - 1) * (2 * n) := by
          have h_gt_plus : 2 * n.factorial > 2 * n * (2 * n + 1) := factorial_gt_two_n_mul_two_n_plus_one hn
          have h_ineq : 2 * n * (2 * n + 1) > 2 * n * (2 * n - 1) := by
            have : 2 * n + 1 > 2 * n - 1 := by omega
            exact Nat.mul_lt_mul_of_pos_left this (by omega)
          have h_comm : (2 * n - 1) * (2 * n) = 2 * n * (2 * n - 1) := Nat.mul_comm _ _
          rw [h_comm]
          omega
        have h_comm : (2 * p - 1) * (2 * p) = 2 * p * (2 * p - 1) := Nat.mul_comm _ _
        rw [h_comm] at h_eq
        omega
    · calc k + 1 = p * d := hd
        _ ≥ p * 3 := Nat.mul_le_mul_left p hd_ge_3
        _ = 3 * p := by ring

lemma k_ge_D_p {n k p D : ℕ} (h_eq : 2 * n.factorial = k * (k + 1))
    (hp_prime : Nat.Prime p) (hp_le : p ≤ n)
    (h_gt : 2 * n.factorial > (D - 1) * n * ((D - 1) * n + 1)) (hD : D ≥ 2) :
    k + 1 ≥ D * p := by
  have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  have hp_dvd_two_fact : p ∣ 2 * n.factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
  rw [h_eq] at hp_dvd_two_fact
  cases' Nat.Prime.dvd_mul hp_prime |>.mp hp_dvd_two_fact with hpk hpk1
  · obtain ⟨a, ha⟩ := hpk
    have ha_pos : a > 0 := by
      by_contra hc
      have : a = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    rcases lt_or_ge a D with ha_lt | ha_ge
    · have ha_le : a ≤ D - 1 := by omega
      have hk_le : k * (k + 1) ≤ (D - 1) * n * ((D - 1) * n + 1) := by
        rw [ha]
        have h1 : p * a ≤ (D - 1) * n := by
          have : p * a ≤ n * (D - 1) := Nat.mul_le_mul hp_le ha_le
          rwa [Nat.mul_comm n (D - 1)] at this
        have h2 : p * a + 1 ≤ (D - 1) * n + 1 := by omega
        exact Nat.mul_le_mul h1 h2
      omega
    · have hk_ge : k ≥ D * p := by
        calc k = p * a := ha
          _ ≥ p * D := Nat.mul_le_mul_left p ha_ge
          _ = D * p := by ring
      omega
  · obtain ⟨b, hb⟩ := hpk1
    have hb_pos : b > 0 := by
      by_contra hc
      have : b = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    rcases lt_or_ge b D with hb_lt | hb_ge
    · have hb_le : b ≤ D - 1 := by omega
      have hk_le : k * (k + 1) ≤ (D - 1) * n * ((D - 1) * n + 1) := by
        have h_bp : k + 1 = b * p := by rw [Nat.mul_comm b p]; exact hb
        have hk_eq : k = b * p - 1 := by omega
        rw [h_bp, hk_eq]
        have h2 : b * p ≤ (D - 1) * n := Nat.mul_le_mul hb_le hp_le
        have h1 : b * p - 1 ≤ (D - 1) * n := by omega
        have h3 : (D - 1) * n ≤ (D - 1) * n + 1 := by omega
        have h4 : b * p ≤ (D - 1) * n + 1 := h2.trans h3
        exact Nat.mul_le_mul h1 h4
      omega
    · calc k + 1 = p * b := hb
        _ ≥ p * D := Nat.mul_le_mul_left p hb_ge
        _ = D * p := by ring

lemma two_pow_61_dvd_factorial_67 : 2^61 ∣ (67).factorial := by decide

lemma two_pow_61_dvd_factorial {n : ℕ} (hn : 67 ≤ n) : 2^61 ∣ n.factorial := by
  have h_dvd : (67).factorial ∣ n.factorial := Nat.factorial_dvd_factorial hn
  exact dvd_trans two_pow_61_dvd_factorial_67 h_dvd

lemma two_pow_62_dvd_two_factorial {n : ℕ} (hn : 67 ≤ n) : 2^62 ∣ 2 * n.factorial := by
  have h1 : 2^62 = 2 * 2^61 := by ring
  rw [h1]
  have h2 : 2^61 ∣ n.factorial := two_pow_61_dvd_factorial hn
  exact Nat.mul_dvd_mul_left 2 h2

def D : ℕ := 4031017571163409250897522631853874805931471009

lemma factorial_gt_huge {n : ℕ} (hn : 67 ≤ n) : 2 * n.factorial > (D - 1) * n * ((D - 1) * n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial > (D - 1) * m * ((D - 1) * m + 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) > (m + 1) * ((D - 1) * m * ((D - 1) * m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left ih' (by omega)
    have h2 : (m + 1) * ((D - 1) * m * ((D - 1) * m + 1)) ≥ (D - 1) * (m + 1) * ((D - 1) * (m + 1) + 1) := by
      have h_comm1 : (m + 1) * ((D - 1) * m * ((D - 1) * m + 1)) = (D - 1) * (m + 1) * (m * ((D - 1) * m + 1)) := by ring
      rw [h_comm1]
      have h3 : m * ((D - 1) * m + 1) ≥ (D - 1) * (m + 1) + 1 := by
        have h_mul1 : m * ((D - 1) * m + 1) = (D - 1) * m * m + m := by ring
        have h_mul2 : (D - 1) * (m + 1) + 1 = (D - 1) * m + D := by unfold D; omega
        rw [h_mul1, h_mul2]
        have h_quad : (D - 1) * m * m ≥ (D - 1) * m + D := by
          calc (D - 1) * m * m = ((D - 1) * m) * m := by ring
            _ ≥ ((D - 1) * m) * 67 := Nat.mul_le_mul_left _ hm
            _ = (D - 1) * m * 1 + (D - 1) * m * 66 := by ring
            _ ≥ (D - 1) * m * 1 + (D - 1) * 67 * 66 := by
              have : (D - 1) * m * 66 ≥ (D - 1) * 67 * 66 := by
                have : (D - 1) * m ≥ (D - 1) * 67 := Nat.mul_le_mul_left _ hm
                omega
              omega
            _ ≥ (D - 1) * m + D := by
              have : (D - 1) * 67 * 66 ≥ D := by
                unfold D; omega
              omega
        unfold D at h_quad ⊢
        omega
      exact Nat.mul_le_mul_left _ h3
    exact lt_of_le_of_lt h2 h1

lemma coprime_dvd_mul {q c A B : ℕ} (hq : Nat.Prime q) (h_coprime : Nat.Coprime A B) (h_dvd : q^c ∣ A * B) :
  q^c ∣ A ∨ q^c ∣ B := by
  by_cases hqA : q ∣ A
  · left
    have hqB : ¬ q ∣ B := by
      intro hqB
      have h_div : q ∣ Nat.gcd A B := Nat.dvd_gcd hqA hqB
      rw [h_coprime.gcd_eq_one] at h_div
      exact Nat.Prime.not_dvd_one hq h_div
    have h_cop : Nat.Coprime (q^c) B := hq.coprime_iff_not_dvd.mpr hqB |>.pow_left c
    have h_dvd' : q^c ∣ B * A := by rw [Nat.mul_comm B A]; exact h_dvd
    exact h_cop.dvd_of_dvd_mul_left h_dvd'
  · right
    have h_cop : Nat.Coprime (q^c) A := hq.coprime_iff_not_dvd.mpr hqA |>.pow_left c
    have h_dvd' : q^c ∣ A * B := h_dvd
    exact h_cop.dvd_of_dvd_mul_left h_dvd'

lemma two_pow_62_dvd_k_or_k_add_one {n k : ℕ} (h_eq : 2 * n.factorial = k * (k + 1)) (hn : 67 ≤ n) :
    2^62 ∣ k ∨ 2^62 ∣ k + 1 := by
  have h_dvd : 2^62 ∣ k * (k + 1) := by
    rw [← h_eq]
    exact two_pow_62_dvd_two_factorial hn
  have h_cop : Nat.Coprime k (k + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right k
  have h_prime : Nat.Prime 2 := Nat.prime_two
  exact coprime_dvd_mul h_prime h_cop h_dvd

lemma k_ge_two_pow_62 {n k : ℕ} (h_eq : 2 * n.factorial = k * (k + 1)) (hn : 67 ≤ n) :
    k + 1 ≥ 2^62 := by
  have h_cases : 2^62 ∣ k ∨ 2^62 ∣ k + 1 := two_pow_62_dvd_k_or_k_add_one h_eq hn
  rcases h_cases with ⟨y, hy⟩ | ⟨y, hy⟩
  · have hy_pos : y > 0 := by
      by_contra hc
      have : y = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    have hk_ge : k ≥ 2^62 := by
      calc k = 2^62 * y := hy
        _ ≥ 2^62 * 1 := Nat.mul_le_mul_left _ (by omega)
        _ = 2^62 := by ring
    omega
  · have hy_pos : y > 0 := by
      by_contra hc
      have : y = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    calc k + 1 = 2^62 * y := hy
      _ ≥ 2^62 * 1 := Nat.mul_le_mul_left _ (by omega)
      _ = 2^62 := by ring

lemma prime_factor_of_8_factorial_add_one {n : ℕ} (_hn : 2 ≤ n) (y : ℕ) (hy : y * y = 8 * n.factorial + 1) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ y ∧ q > n := by
  have hy_gt_1 : y > 1 := by
    by_contra hc
    have : y = 0 ∨ y = 1 := by omega
    rcases this with rfl | rfl
    · have : n.factorial > 0 := Nat.factorial_pos n
      omega
    · have : n.factorial > 0 := Nat.factorial_pos n
      omega
  have hy_ne1 : y ≠ 1 := by omega
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hy_ne1
  use q
  refine ⟨hq_prime, hq_dvd, ?_⟩
  by_contra hc
  have hq_le : q ≤ n := by omega
  have hq_dvd_fact : q ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hq_prime) hq_le
  have hq_dvd_8_fact : q ∣ 8 * n.factorial := dvd_mul_of_dvd_right hq_dvd_fact 8
  have hq_dvd_y2 : q ∣ y * y := by
    have : y * y = y^2 := by ring
    rw [this]
    exact dvd_pow hq_dvd (by omega)
  rw [hy] at hq_dvd_y2
  have hq_dvd_1 : q ∣ 1 := (Nat.dvd_add_right hq_dvd_8_fact).mp hq_dvd_y2
  have : q = 1 := Nat.dvd_one.mp hq_dvd_1
  subst this
  exact Nat.Prime.ne_one hq_prime rfl

lemma not_triangular_of_ge_67 {n : ℕ} (hn : 67 ≤ n) : ¬ is_triangular n.factorial := by
  rintro ⟨k, hk⟩
  have h_eq : 2 * n.factorial = k * (k + 1) := by
    rw [← k_mul_k_add_one_div_two_mul_two k, ← hk]
    ring
  rcases eq_or_ne n 67 with rfl | hn_ne
  · have hp_prime : Nat.Prime 67 := by decide
    have hp_le : 67 ≤ 67 := by omega
    have h_gt : 2 * (67).factorial > (D - 1) * 67 * ((D - 1) * 67 + 1) := factorial_gt_huge (by omega)
    have hk_ge : k + 1 ≥ D * 67 := k_ge_D_p h_eq hp_prime hp_le h_gt (by decide)
    have h_lt : 2 * (67).factorial < (D * 67 - 1) * (D * 67) := by decide
    have hk_le : k * (k + 1) < (D * 67 - 1) * (D * 67) := by omega
    have hk_ge2 : k * (k + 1) ≥ (D * 67 - 1) * (D * 67) := by
      have : k ≥ D * 67 - 1 := by omega
      exact Nat.mul_le_mul this hk_ge
    omega
  · have hn_ge : 68 ≤ n := by omega
    sorry


theorem not_triangular_6 : ¬ is_triangular (factorial 6) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 11, y^2 = (8 * factorial 6 + 1 : ZMod 11) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 6 + 1) 11 h_zmod

theorem not_triangular_7 : ¬ is_triangular (factorial 7) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 11, y^2 = (8 * factorial 7 + 1 : ZMod 11) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 7 + 1) 11 h_zmod

theorem not_triangular_8 : ¬ is_triangular (factorial 8) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 11, y^2 = (8 * factorial 8 + 1 : ZMod 11) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 8 + 1) 11 h_zmod

theorem not_triangular_9 : ¬ is_triangular (factorial 9) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 13, y^2 = (8 * factorial 9 + 1 : ZMod 13) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 9 + 1) 13 h_zmod

theorem not_triangular_10 : ¬ is_triangular (factorial 10) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 17, y^2 = (8 * factorial 10 + 1 : ZMod 17) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 10 + 1) 17 h_zmod

theorem not_triangular_11 : ¬ is_triangular (factorial 11) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 19, y^2 = (8 * factorial 11 + 1 : ZMod 19) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 11 + 1) 19 h_zmod

theorem not_triangular_12 : ¬ is_triangular (factorial 12) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 13, y^2 = (8 * factorial 12 + 1 : ZMod 13) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 12 + 1) 13 h_zmod

theorem not_triangular_13 : ¬ is_triangular (factorial 13) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 19, y^2 = (8 * factorial 13 + 1 : ZMod 19) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 13 + 1) 19 h_zmod

theorem not_triangular_14 : ¬ is_triangular (factorial 14) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 17, y^2 = (8 * factorial 14 + 1 : ZMod 17) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 14 + 1) 17 h_zmod

theorem not_triangular_15 : ¬ is_triangular (factorial 15) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 19, y^2 = (8 * factorial 15 + 1 : ZMod 19) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 15 + 1) 19 h_zmod

theorem not_triangular_16 : ¬ is_triangular (factorial 16) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 17, y^2 = (8 * factorial 16 + 1 : ZMod 17) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 16 + 1) 17 h_zmod

theorem not_triangular_17 : ¬ is_triangular (factorial 17) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 23, y^2 = (8 * factorial 17 + 1 : ZMod 23) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 17 + 1) 23 h_zmod

theorem not_triangular_18 : ¬ is_triangular (factorial 18) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 41, y^2 = (8 * factorial 18 + 1 : ZMod 41) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 18 + 1) 41 h_zmod

theorem not_triangular_19 : ¬ is_triangular (factorial 19) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 23, y^2 = (8 * factorial 19 + 1 : ZMod 23) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 19 + 1) 23 h_zmod

theorem not_triangular_20 : ¬ is_triangular (factorial 20) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 23, y^2 = (8 * factorial 20 + 1 : ZMod 23) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 20 + 1) 23 h_zmod

theorem not_triangular_21 : ¬ is_triangular (factorial 21) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 29, y^2 = (8 * factorial 21 + 1 : ZMod 29) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 21 + 1) 29 h_zmod

theorem not_triangular_22 : ¬ is_triangular (factorial 22) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 31, y^2 = (8 * factorial 22 + 1 : ZMod 31) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 22 + 1) 31 h_zmod

theorem not_triangular_23 : ¬ is_triangular (factorial 23) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 29, y^2 = (8 * factorial 23 + 1 : ZMod 29) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 23 + 1) 29 h_zmod

theorem not_triangular_24 : ¬ is_triangular (factorial 24) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 31, y^2 = (8 * factorial 24 + 1 : ZMod 31) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 24 + 1) 31 h_zmod

theorem not_triangular_25 : ¬ is_triangular (factorial 25) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 29, y^2 = (8 * factorial 25 + 1 : ZMod 29) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 25 + 1) 29 h_zmod

theorem not_triangular_26 : ¬ is_triangular (factorial 26) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 29, y^2 = (8 * factorial 26 + 1 : ZMod 29) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 26 + 1) 29 h_zmod

theorem not_triangular_27 : ¬ is_triangular (factorial 27) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 31, y^2 = (8 * factorial 27 + 1 : ZMod 31) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 27 + 1) 31 h_zmod

theorem not_triangular_28 : ¬ is_triangular (factorial 28) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 37, y^2 = (8 * factorial 28 + 1 : ZMod 37) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 28 + 1) 37 h_zmod

theorem not_triangular_29 : ¬ is_triangular (factorial 29) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 37, y^2 = (8 * factorial 29 + 1 : ZMod 37) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 29 + 1) 37 h_zmod

theorem not_triangular_30 : ¬ is_triangular (factorial 30) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 31, y^2 = (8 * factorial 30 + 1 : ZMod 31) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 30 + 1) 31 h_zmod

theorem not_triangular_31 : ¬ is_triangular (factorial 31) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 37, y^2 = (8 * factorial 31 + 1 : ZMod 37) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 31 + 1) 37 h_zmod

theorem not_triangular_32 : ¬ is_triangular (factorial 32) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 37, y^2 = (8 * factorial 32 + 1 : ZMod 37) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 32 + 1) 37 h_zmod

theorem not_triangular_33 : ¬ is_triangular (factorial 33) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 41, y^2 = (8 * factorial 33 + 1 : ZMod 41) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 33 + 1) 41 h_zmod

theorem not_triangular_34 : ¬ is_triangular (factorial 34) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 41, y^2 = (8 * factorial 34 + 1 : ZMod 41) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 34 + 1) 41 h_zmod

theorem not_triangular_35 : ¬ is_triangular (factorial 35) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 41, y^2 = (8 * factorial 35 + 1 : ZMod 41) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 35 + 1) 41 h_zmod

theorem not_triangular_36 : ¬ is_triangular (factorial 36) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 41, y^2 = (8 * factorial 36 + 1 : ZMod 41) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 36 + 1) 41 h_zmod

theorem not_triangular_37 : ¬ is_triangular (factorial 37) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 47, y^2 = (8 * factorial 37 + 1 : ZMod 47) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 37 + 1) 47 h_zmod

theorem not_triangular_38 : ¬ is_triangular (factorial 38) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 41, y^2 = (8 * factorial 38 + 1 : ZMod 41) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 38 + 1) 41 h_zmod

theorem not_triangular_39 : ¬ is_triangular (factorial 39) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 61, y^2 = (8 * factorial 39 + 1 : ZMod 61) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 39 + 1) 61 h_zmod

theorem not_triangular_40 : ¬ is_triangular (factorial 40) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 41, y^2 = (8 * factorial 40 + 1 : ZMod 41) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 40 + 1) 41 h_zmod

theorem not_triangular_41 : ¬ is_triangular (factorial 41) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 47, y^2 = (8 * factorial 41 + 1 : ZMod 47) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 41 + 1) 47 h_zmod

theorem not_triangular_42 : ¬ is_triangular (factorial 42) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 53, y^2 = (8 * factorial 42 + 1 : ZMod 53) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 42 + 1) 53 h_zmod

theorem not_triangular_43 : ¬ is_triangular (factorial 43) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 53, y^2 = (8 * factorial 43 + 1 : ZMod 53) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 43 + 1) 53 h_zmod

theorem not_triangular_44 : ¬ is_triangular (factorial 44) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 47, y^2 = (8 * factorial 44 + 1 : ZMod 47) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 44 + 1) 47 h_zmod

theorem not_triangular_45 : ¬ is_triangular (factorial 45) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 53, y^2 = (8 * factorial 45 + 1 : ZMod 53) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 45 + 1) 53 h_zmod

theorem not_triangular_46 : ¬ is_triangular (factorial 46) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 47, y^2 = (8 * factorial 46 + 1 : ZMod 47) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 46 + 1) 47 h_zmod

theorem not_triangular_47 : ¬ is_triangular (factorial 47) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 59, y^2 = (8 * factorial 47 + 1 : ZMod 59) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 47 + 1) 59 h_zmod

theorem not_triangular_48 : ¬ is_triangular (factorial 48) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 59, y^2 = (8 * factorial 48 + 1 : ZMod 59) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 48 + 1) 59 h_zmod

theorem not_triangular_49 : ¬ is_triangular (factorial 49) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 53, y^2 = (8 * factorial 49 + 1 : ZMod 53) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 49 + 1) 53 h_zmod

theorem not_triangular_50 : ¬ is_triangular (factorial 50) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 53, y^2 = (8 * factorial 50 + 1 : ZMod 53) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 50 + 1) 53 h_zmod

theorem not_triangular_51 : ¬ is_triangular (factorial 51) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 59, y^2 = (8 * factorial 51 + 1 : ZMod 59) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 51 + 1) 59 h_zmod

theorem not_triangular_52 : ¬ is_triangular (factorial 52) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 71, y^2 = (8 * factorial 52 + 1 : ZMod 71) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 52 + 1) 71 h_zmod

theorem not_triangular_53 : ¬ is_triangular (factorial 53) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 61, y^2 = (8 * factorial 53 + 1 : ZMod 61) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 53 + 1) 61 h_zmod

theorem not_triangular_54 : ¬ is_triangular (factorial 54) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 59, y^2 = (8 * factorial 54 + 1 : ZMod 59) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 54 + 1) 59 h_zmod

theorem not_triangular_55 : ¬ is_triangular (factorial 55) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 71, y^2 = (8 * factorial 55 + 1 : ZMod 71) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 55 + 1) 71 h_zmod

theorem not_triangular_56 : ¬ is_triangular (factorial 56) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 59, y^2 = (8 * factorial 56 + 1 : ZMod 59) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 56 + 1) 59 h_zmod

theorem not_triangular_57 : ¬ is_triangular (factorial 57) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 61, y^2 = (8 * factorial 57 + 1 : ZMod 61) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 57 + 1) 61 h_zmod

theorem not_triangular_58 : ¬ is_triangular (factorial 58) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 59, y^2 = (8 * factorial 58 + 1 : ZMod 59) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 58 + 1) 59 h_zmod

theorem not_triangular_59 : ¬ is_triangular (factorial 59) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 89, y^2 = (8 * factorial 59 + 1 : ZMod 89) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 59 + 1) 89 h_zmod

theorem not_triangular_60 : ¬ is_triangular (factorial 60) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 61, y^2 = (8 * factorial 60 + 1 : ZMod 61) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 60 + 1) 61 h_zmod

theorem not_triangular_61 : ¬ is_triangular (factorial 61) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 73, y^2 = (8 * factorial 61 + 1 : ZMod 73) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 61 + 1) 73 h_zmod

theorem not_triangular_62 : ¬ is_triangular (factorial 62) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 73, y^2 = (8 * factorial 62 + 1 : ZMod 73) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 62 + 1) 73 h_zmod

theorem not_triangular_63 : ¬ is_triangular (factorial 63) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 73, y^2 = (8 * factorial 63 + 1 : ZMod 73) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 63 + 1) 73 h_zmod

theorem not_triangular_64 : ¬ is_triangular (factorial 64) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 79, y^2 = (8 * factorial 64 + 1 : ZMod 79) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 64 + 1) 79 h_zmod

theorem not_triangular_65 : ¬ is_triangular (factorial 65) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 73, y^2 = (8 * factorial 65 + 1 : ZMod 73) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 65 + 1) 73 h_zmod

theorem not_triangular_66 : ¬ is_triangular (factorial 66) := by
  apply not_triangular_of_not_square
  have h_zmod : ¬ ∃ y : ZMod 73, y^2 = (8 * factorial 66 + 1 : ZMod 73) := by decide
  exact not_square_of_not_square_zmod (8 * factorial 66 + 1) 73 h_zmod

theorem oeis_338489_conjecture_0 :
    ∀ n : ℕ, is_triangular n.factorial ↔ n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5 := by
  intro n
  constructor
  · intro h
    rcases lt_or_ge n 6 with hn | hn
    · interval_cases n
      · left; rfl
      · right; left; rfl
      · rw [is_triangular_iff_dec] at h
        -- factorial 2 is 2
        -- is_triangular_dec 2 = false
        -- so h is false
        revert h; decide
      · right; right; left; rfl
      · rw [is_triangular_iff_dec] at h
        revert h; decide
      · right; right; right; rfl
    · rcases lt_or_ge n 67 with hn_lt | hn_ge
      · interval_cases n
        · exfalso; exact not_triangular_6 h
        · exfalso; exact not_triangular_7 h
        · exfalso; exact not_triangular_8 h
        · exfalso; exact not_triangular_9 h
        · exfalso; exact not_triangular_10 h
        · exfalso; exact not_triangular_11 h
        · exfalso; exact not_triangular_12 h
        · exfalso; exact not_triangular_13 h
        · exfalso; exact not_triangular_14 h
        · exfalso; exact not_triangular_15 h
        · exfalso; exact not_triangular_16 h
        · exfalso; exact not_triangular_17 h
        · exfalso; exact not_triangular_18 h
        · exfalso; exact not_triangular_19 h
        · exfalso; exact not_triangular_20 h
        · exfalso; exact not_triangular_21 h
        · exfalso; exact not_triangular_22 h
        · exfalso; exact not_triangular_23 h
        · exfalso; exact not_triangular_24 h
        · exfalso; exact not_triangular_25 h
        · exfalso; exact not_triangular_26 h
        · exfalso; exact not_triangular_27 h
        · exfalso; exact not_triangular_28 h
        · exfalso; exact not_triangular_29 h
        · exfalso; exact not_triangular_30 h
        · exfalso; exact not_triangular_31 h
        · exfalso; exact not_triangular_32 h
        · exfalso; exact not_triangular_33 h
        · exfalso; exact not_triangular_34 h
        · exfalso; exact not_triangular_35 h
        · exfalso; exact not_triangular_36 h
        · exfalso; exact not_triangular_37 h
        · exfalso; exact not_triangular_38 h
        · exfalso; exact not_triangular_39 h
        · exfalso; exact not_triangular_40 h
        · exfalso; exact not_triangular_41 h
        · exfalso; exact not_triangular_42 h
        · exfalso; exact not_triangular_43 h
        · exfalso; exact not_triangular_44 h
        · exfalso; exact not_triangular_45 h
        · exfalso; exact not_triangular_46 h
        · exfalso; exact not_triangular_47 h
        · exfalso; exact not_triangular_48 h
        · exfalso; exact not_triangular_49 h
        · exfalso; exact not_triangular_50 h
        · exfalso; exact not_triangular_51 h
        · exfalso; exact not_triangular_52 h
        · exfalso; exact not_triangular_53 h
        · exfalso; exact not_triangular_54 h
        · exfalso; exact not_triangular_55 h
        · exfalso; exact not_triangular_56 h
        · exfalso; exact not_triangular_57 h
        · exfalso; exact not_triangular_58 h
        · exfalso; exact not_triangular_59 h
        · exfalso; exact not_triangular_60 h
        · exfalso; exact not_triangular_61 h
        · exfalso; exact not_triangular_62 h
        · exfalso; exact not_triangular_63 h
        · exfalso; exact not_triangular_64 h
        · exfalso; exact not_triangular_65 h
        · exfalso; exact not_triangular_66 h
      · exfalso; exact not_triangular_of_ge_67 hn_ge h
  · rintro (rfl | rfl | rfl | rfl)
    · use 1; rfl
    · use 1; rfl
    · use 3; rfl
    · use 15; rfl

